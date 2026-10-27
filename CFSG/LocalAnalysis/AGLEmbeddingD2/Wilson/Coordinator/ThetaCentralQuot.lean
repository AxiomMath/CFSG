module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.ThetaCore

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator

open CFSG.RankThree.LocalRank Subgroup

theorem center_eq_bot_of_isSimpleGroup {H : Type*} [Group H] [IsSimpleGroup H]
    (hnc : ∃ a b : H, a * b ≠ b * a) : center H = ⊥ := by
  rcases (inferInstance : (center H).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    exact hab ((mem_center_iff.mp (h ▸ mem_top b)) a)

theorem eq_bot_of_normal_of_isSolvable {H : Type*} [Group H] [IsSimpleGroup H]
    (hnc : ∃ a b : H, a * b ≠ b * a) {M : Subgroup H} (hM : M.Normal)
    (hs : Group.IsSolvable M) : M = ⊥ := by
  rcases hM.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hHs : Group.IsSolvable H := by
      have : Group.IsSolvable (⊤ : Subgroup H) := h ▸ hs
      exact Group.isSolvable_of_surjective (f := (⊤ : Subgroup H).subtype)
        (fun k => ⟨⟨k, mem_top k⟩, rfl⟩)
    obtain ⟨a, b, hab⟩ := hnc
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hHs) a b)

theorem exists_mul_ne_of_center_eq_bot {H : Type*} [Group H] [Nontrivial H]
    (hc : center H = ⊥) : ∃ a b : H, a * b ≠ b * a := by
  by_contra h
  push Not at h
  obtain ⟨a, ha⟩ := exists_ne (1 : H)
  have : a ∈ center H := mem_center_iff.mpr fun g => h g a
  rw [hc, mem_bot] at this
  exact ha this

theorem isSimpleGroup_of_center_eq_bot {H : Type*} [Group H] [IsSimpleGroup (H ⧸ center H)]
    (hc : center H = ⊥) : IsSimpleGroup H :=
  ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.isSimpleGroup

variable {G Q : Type*} [Group G] [Group Q]

theorem aschbacherSolvableCore_eq_bot_of_quot [Finite G] {K : Type*} [Field K] [Finite K]
    {q : G →* Q} (hqs : Function.Surjective q) (hZ : q.ker ≤ center G) {n : ℕ}
    (hn : Nat.card q.ker = n) (hexp : ∀ u : Kˣ, u ^ (3 * n) = 1) {x : G}
    (hmap : (centralizer ({x} : Set G)).map q = centralizer ({q x} : Set Q))
    {L : Subgroup G} (hLC : L ≤ centralizer ({x} : Set G)) [IsSimpleGroup L]
    (hnc : ∃ a b : L, a * b ≠ b * a) (ψ : centralizer ({x} : Set G) →* Kˣ)
    (hψ : ψ.ker = L.subgroupOf (centralizer ({x} : Set G))) :
    aschbacherSolvableCore 3 (centralizer ({q x} : Set Q)) = ⊥ := by
  have : Finite Q := Finite.of_surjective q hqs
  set N := thetaOf (q x) with hN
  have hcen : center L = ⊥ := center_eq_bot_of_isSimpleGroup hnc
  have hψL : ∀ c (hc : c ∈ centralizer ({x} : Set G)), ψ ⟨c, hc⟩ = 1 ↔ c ∈ L := by
    intro c hc
    rw [← MonoidHom.mem_ker, hψ, mem_subgroupOf]
  have hLn : ∀ c ∈ centralizer ({x} : Set G), ∀ l ∈ L, c * l * c⁻¹ ∈ L := by
    intro c hc l hl
    rw [← hψL _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hc (hLC hl)) (Subgroup.inv_mem _ hc))]
    change ψ (⟨c, hc⟩ * ⟨l, hLC hl⟩ * ⟨c, hc⟩⁻¹) = 1
    rw [map_mul, map_mul, (hψL l (hLC hl)).mpr hl, mul_one, map_inv, mul_inv_cancel]
  have hqC : ∀ c ∈ centralizer ({x} : Set G), q c ∈ centralizer ({q x} : Set Q) := fun c hc =>
    hmap ▸ mem_map_of_mem q hc
  have hLN : ∀ l ∈ L, q l ∈ N → l = 1 := by
    set M : Subgroup L := (N.comap q).subgroupOf L with hM
    have hMn : M.Normal := by
      refine ⟨fun m hm g => ?_⟩
      rw [hM, mem_subgroupOf, mem_comap] at hm ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      exact thetaOf_conj (hqC _ (hLC g.2)) hm
    have hMs : Group.IsSolvable M := by
      have := thetaOf_isSolvable (q x)
      let f : M →* N :=
        { toFun := fun m => ⟨q ((m : L) : G), mem_comap.mp (mem_subgroupOf.mp m.2)⟩
          map_one' := by ext; simp
          map_mul' := fun a b => by ext; simp }
      refine Group.isSolvable_of_isSolvable_injective (f := f) fun a b hab => ?_
      have h1 : q ((a : L) : G) = q ((b : L) : G) := congrArg Subtype.val hab
      have hk : ((a : L) : G)⁻¹ * ((b : L) : G) ∈ q.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
      have hz : (a : L)⁻¹ * (b : L) ∈ center L := by
        rw [mem_center_iff]
        intro w
        apply Subtype.ext
        exact mem_center_iff.mp (hZ hk) (w : G)
      rw [hcen, mem_bot] at hz
      exact Subtype.ext (inv_mul_eq_one.mp hz)
    have hMbot := eq_bot_of_normal_of_isSolvable hnc hMn hMs
    intro l hl hlN
    have : (⟨l, hl⟩ : L) ∈ M := by rw [hM, mem_subgroupOf, mem_comap]; exact hlN
    rw [hMbot, mem_bot] at this
    exact congrArg Subtype.val this
  set D : Subgroup G := centralizer ({x} : Set G) ⊓ centralizer (L : Set G) with hD
  have hcomm : ∀ c ∈ centralizer ({x} : Set G), q c ∈ N → c ∈ D := by
    intro c hc hcN
    refine mem_inf.mpr ⟨hc, mem_centralizer_iff.mpr fun l hl => ?_⟩
    have hk : c * l * c⁻¹ * l⁻¹ ∈ L := L.mul_mem (hLn c hc l hl) (L.inv_mem hl)
    have hkN : q (c * l * c⁻¹ * l⁻¹) ∈ N := by
      have h1 : q l * (q c)⁻¹ * (q l)⁻¹ ∈ N := thetaOf_conj (hqC l (hLC hl)) (N.inv_mem hcN)
      have := N.mul_mem hcN h1
      simpa only [map_mul, map_inv, mul_assoc] using this
    have h1 := hLN _ hk hkN
    calc l * c = (c * l * c⁻¹ * l⁻¹)⁻¹ * (c * l) := by group
      _ = c * l := by rw [h1, inv_one, one_mul]
  have hDC : D ≤ centralizer ({x} : Set G) := inf_le_left
  set ψD : D →* Kˣ := ψ.comp (inclusion hDC) with hψD
  have hψDinj : Function.Injective ψD := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have hdL : (d : G) ∈ L := (hψL d (hDC d.2)).mp hd
    have : (⟨d, hdL⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro w
      apply Subtype.ext
      exact (mem_centralizer_iff.mp (mem_inf.mp d.2).2) w w.2
    rw [hcen, mem_bot] at this
    have hd1 : (d : G) = 1 := congrArg Subtype.val this
    exact Subtype.ext hd1
  have hkerD : q.ker ≤ D := fun z hz => mem_inf.mpr
    ⟨mem_centralizer_singleton_iff.mpr (mem_center_iff.mp (hZ hz) x).symm,
      mem_centralizer_iff.mpr fun l _ => mem_center_iff.mp (hZ hz) l⟩
  have hn0 : 0 < n := hn ▸ Nat.card_pos
  have : NeZero n := ⟨hn0.ne'⟩
  have hzn : ∀ z ∈ q.ker, z ^ n = 1 := by
    intro z hz
    have := pow_card_eq_one' (G := q.ker) (x := ⟨z, hz⟩)
    rw [hn] at this
    simpa using congrArg Subtype.val this
  have hroot : ∀ d : D, d ^ n = 1 → (d : G) ∈ q.ker := by
    intro d hd
    let f : q.ker → rootsOfUnity n K := fun z =>
      ⟨ψD ⟨z, hkerD z.2⟩, by
        rw [mem_rootsOfUnity, ← map_pow]
        have : (⟨z, hkerD z.2⟩ : D) ^ n = 1 := Subtype.ext (by simpa using hzn z z.2)
        rw [this, map_one]⟩
    have hf : Function.Injective f := by
      intro a b hab
      have h1 := hψDinj (congrArg Subtype.val hab)
      have h2 : (a : G) = b := congrArg (fun w : D => (w : G)) h1
      exact Subtype.ext h2
    have hcard : Nat.card (rootsOfUnity n K) ≤ Nat.card q.ker := by
      rw [hn]
      exact card_rootsOfUnity K n
    obtain ⟨z, hz⟩ := (hf.bijective_of_nat_card_le hcard).2
      ⟨ψD d, by rw [mem_rootsOfUnity, ← map_pow, hd, map_one]⟩
    have h1 := hψDinj (congrArg Subtype.val hz)
    rw [← h1]
    exact z.2
  have hcube : ∀ c ∈ centralizer ({x} : Set G), q c ∈ N → q c ^ 3 = 1 := by
    intro c hc hcN
    have hcD := hcomm c hc hcN
    have h1 : (⟨c, hcD⟩ : D) ^ (3 * n) = 1 := hψDinj (by rw [map_pow, hexp, map_one])
    have h2 : ((⟨c, hcD⟩ : D) ^ 3) ^ n = 1 := by rw [← pow_mul, h1]
    have h3 := hroot _ h2
    rw [MonoidHom.mem_ker] at h3
    rw [← map_pow]
    simpa using h3
  have hNbot : N = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    rw [mem_bot]
    have hmC : m ∈ centralizer ({q x} : Set Q) := thetaOf_le (q x) hm
    rw [← hmap] at hmC
    obtain ⟨c, hc, rfl⟩ := mem_map.mp hmC
    have h3 := hcube c hc hm
    by_contra hm1
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf (⟨q c, hm⟩ : N) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime h3 hm1
    exact thetaOf_not_three_dvd (q x) (hord ▸ orderOf_dvd_natCard _)
  rw [hN, thetaOf] at hNbot
  exact (map_eq_bot_iff_of_injective _ (centralizer ({q x} : Set Q)).subtype_injective).mp hNbot

end CFSG.AGLEmbeddingD2.Wilson.Coordinator
