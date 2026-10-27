module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.FiveTwentySix

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.QuasithinUnique

open scoped commutatorElement

variable {X : Type*} [Group X]

private theorem conj_mem_pElementSubgroup_two {A : Subgroup X} {a : X} (ha : a ∈ A) {x : X}
    (hx : x ∈ pElementSubgroup 2 A) : a * x * a⁻¹ ∈ pElementSubgroup 2 A := by
  unfold pElementSubgroup at hx ⊢
  refine Subgroup.closure_induction
    (p := fun y _ => a * y * a⁻¹ ∈ Subgroup.closure {z : X | z ∈ A ∧ ∃ k : ℕ, orderOf z = 2 ^ k})
    ?_ ?_ ?_ ?_ hx
  · rintro y ⟨hyA, k, hk⟩
    refine Subgroup.subset_closure ⟨A.mul_mem (A.mul_mem ha hyA) (A.inv_mem ha), k, ?_⟩
    have hord : orderOf (a * y * a⁻¹) = orderOf y := by
      simpa only [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj a) y
    rw [hord, hk]
  · simpa using Subgroup.one_mem (Subgroup.closure {z : X | z ∈ A ∧ ∃ k : ℕ, orderOf z = 2 ^ k})
  · intro y z _ _ hy hz
    rw [show a * (y * z) * a⁻¹ = (a * y * a⁻¹) * (a * z * a⁻¹) by group]
    exact Subgroup.mul_mem _ hy hz
  · intro y _ hy
    rw [show a * y⁻¹ * a⁻¹ = (a * y * a⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ hy

private theorem sup_inf_subgroupOf_normal {C P B : Subgroup X} [C.Normal]
    (hCP : C ≤ Subgroup.normalizer (P : Set X))
    (hPB : P ≤ Subgroup.normalizer (B : Set X) ⊔ C) :
    (((P ⊓ Subgroup.normalizer (B : Set X)) ⊔ (P ⊓ C)).subgroupOf P).Normal := by
  have hMP : (P ⊓ Subgroup.normalizer (B : Set X)) ⊔ (P ⊓ C) ≤ P :=
    sup_le inf_le_left inf_le_left
  have hgenH : ∀ p ∈ P, ∀ y ∈ P ⊓ Subgroup.normalizer (B : Set X),
      p * y * p⁻¹ ∈ (P ⊓ Subgroup.normalizer (B : Set X)) ⊔ (P ⊓ C) := by
    intro p hp y hy
    obtain ⟨n, hnB, c, hcC, hnc⟩ :
        ∃ n ∈ Subgroup.normalizer (B : Set X), ∃ c ∈ C, n * c = p := by
      have h := hPB hp
      rwa [Subgroup.mem_sup_of_normal_right] at h
    have hnP : n ∈ Subgroup.normalizer (P : Set X) := by
      have hn : n = p * c⁻¹ := by rw [← hnc]; group
      rw [hn]
      exact (Subgroup.normalizer (P : Set X)).mul_mem (Subgroup.le_normalizer hp)
        ((Subgroup.normalizer (P : Set X)).inv_mem (hCP hcC))
    have hnNB : n ∈ Subgroup.normalizer
        ((Subgroup.normalizer (B : Set X) : Subgroup X) : Set X) :=
      Subgroup.le_normalizer hnB
    have hcP : c ∈ Subgroup.normalizer (P : Set X) := hCP hcC
    obtain ⟨hyP, hyB⟩ := Subgroup.mem_inf.mp hy
    have hcyP : c * y * c⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hcP y).mp hyP
    have hkC : y⁻¹ * c * y * c⁻¹ ∈ C := by
      have h1 : y⁻¹ * c * y ∈ C := by
        simpa using (inferInstance : C.Normal).conj_mem _ hcC y⁻¹
      exact C.mul_mem h1 (C.inv_mem hcC)
    have hkP : y⁻¹ * c * y * c⁻¹ ∈ P := by
      have h := P.mul_mem (P.inv_mem hyP) hcyP
      simpa only [mul_assoc] using h
    have hkK : y⁻¹ * c * y * c⁻¹ ∈ P ⊓ C := Subgroup.mem_inf.mpr ⟨hkP, hkC⟩
    have hcy : c * y * c⁻¹ = y * (y⁻¹ * c * y * c⁻¹) := by group
    have hny : n * y * n⁻¹ ∈ P ⊓ Subgroup.normalizer (B : Set X) :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hnP y).mp hyP,
        (Subgroup.mem_normalizer_iff.mp hnNB y).mp hyB⟩
    have hnk : n * (y⁻¹ * c * y * c⁻¹) * n⁻¹ ∈ P ⊓ C :=
      Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp hnP (y⁻¹ * c * y * c⁻¹)).mp hkP,
          (inferInstance : C.Normal).conj_mem _ hkC n⟩
    have h1 : p * y * p⁻¹ = n * (c * y * c⁻¹) * n⁻¹ := by rw [← hnc]; group
    have h2 : n * (c * y * c⁻¹) * n⁻¹ =
        (n * y * n⁻¹) * (n * (y⁻¹ * c * y * c⁻¹) * n⁻¹) := by rw [hcy]; group
    rw [h1, h2]
    exact Subgroup.mul_mem_sup hny hnk
  have hgenK : ∀ p ∈ P, ∀ y ∈ P ⊓ C,
      p * y * p⁻¹ ∈ (P ⊓ Subgroup.normalizer (B : Set X)) ⊔ (P ⊓ C) := by
    intro p hp y hy
    obtain ⟨n, hnB, c, hcC, hnc⟩ :
        ∃ n ∈ Subgroup.normalizer (B : Set X), ∃ c ∈ C, n * c = p := by
      have h := hPB hp
      rwa [Subgroup.mem_sup_of_normal_right] at h
    have hnP : n ∈ Subgroup.normalizer (P : Set X) := by
      have hn : n = p * c⁻¹ := by rw [← hnc]; group
      rw [hn]
      exact (Subgroup.normalizer (P : Set X)).mul_mem (Subgroup.le_normalizer hp)
        ((Subgroup.normalizer (P : Set X)).inv_mem (hCP hcC))
    have hcP : c ∈ Subgroup.normalizer (P : Set X) := hCP hcC
    obtain ⟨hyP, hyC⟩ := Subgroup.mem_inf.mp hy
    have hcyP : c * y * c⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hcP y).mp hyP
    have hcyC : c * y * c⁻¹ ∈ C := (inferInstance : C.Normal).conj_mem _ hyC c
    have hny : n * (c * y * c⁻¹) * n⁻¹ ∈ P ⊓ C :=
      Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp hnP (c * y * c⁻¹)).mp hcyP,
          (inferInstance : C.Normal).conj_mem _ hcyC n⟩
    have h1 : p * y * p⁻¹ = n * (c * y * c⁻¹) * n⁻¹ := by rw [← hnc]; group
    rw [h1]
    exact Subgroup.mem_sup_right hny
  have hfwd : ∀ p ∈ P, Subgroup.map (MulAut.conj p)
      ((P ⊓ Subgroup.normalizer (B : Set X)) ⊔ (P ⊓ C)) ≤
        (P ⊓ Subgroup.normalizer (B : Set X)) ⊔ (P ⊓ C) := by
    intro p hp
    rw [Subgroup.map_sup, sup_le_iff]
    constructor
    · intro z hz
      obtain ⟨y, hyH, rfl⟩ := Subgroup.mem_map.mp hz
      change p * y * p⁻¹ ∈ (P ⊓ Subgroup.normalizer (B : Set X)) ⊔ (P ⊓ C)
      exact hgenH p hp y hyH
    · intro z hz
      obtain ⟨y, hyK, rfl⟩ := Subgroup.mem_map.mp hz
      change p * y * p⁻¹ ∈ (P ⊓ Subgroup.normalizer (B : Set X)) ⊔ (P ⊓ C)
      exact hgenK p hp y hyK
  refine (Subgroup.normal_subgroupOf_iff hMP).mpr ?_
  intro m p hm hp
  have h1 : (MulAut.conj p) m ∈
      Subgroup.map (MulAut.conj p)
        ((P ⊓ Subgroup.normalizer (B : Set X)) ⊔ (P ⊓ C)) :=
    Subgroup.mem_map_of_mem _ hm
  exact hfwd p hp h1

private theorem not_two_dvd_index_of_isSylowTwoOf_le {P M S : Subgroup X}
    (hSM : S ≤ M) (hS : IsSylowTwoOf S P) (hMP : M ≤ P) :
    ¬ 2 ∣ (M.subgroupOf P).index := by
  intro h2
  apply hS.2.2
  have hle : S.subgroupOf P ≤ M.subgroupOf P := Subgroup.subgroupOf_mono P hSM
  exact h2.trans (Subgroup.index_dvd_of_le hle)

theorem pElementSubgroup_two_le_of_odd_index {P N : Subgroup X} (hNP : N ≤ P)
    (hN : (N.subgroupOf P).Normal) (hodd : ¬ 2 ∣ (N.subgroupOf P).index) :
    pElementSubgroup 2 P ≤ N := by
  letI := hN
  refine (Subgroup.closure_le N).mpr ?_
  rintro x ⟨hxP, k, hxk⟩
  let y : ↥P ⧸ N.subgroupOf P := QuotientGroup.mk' (N.subgroupOf P) ⟨x, hxP⟩
  have hpowP : (⟨x, hxP⟩ : ↥P) ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    show x ^ (2 ^ k) = 1
    rw [← hxk]
    exact pow_orderOf_eq_one x
  have hpow : y ^ (2 ^ k) = 1 := by
    change (QuotientGroup.mk' (N.subgroupOf P) ⟨x, hxP⟩) ^ (2 ^ k) = 1
    rw [← map_pow, hpowP, map_one]
  have hdvd1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hpow
  have hdvd2 : orderOf y ∣ (N.subgroupOf P).index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard y
  have hodd' : Odd (N.subgroupOf P).index :=
    Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])
  have hcop : ((2 : ℕ) ^ k).Coprime (N.subgroupOf P).index :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).pow_left k
  have hone : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  have hy1 : y = 1 := orderOf_eq_one_iff.mp hone
  have hmem : (⟨x, hxP⟩ : ↥P) ∈ N.subgroupOf P :=
    (QuotientGroup.eq_one_iff (⟨x, hxP⟩ : ↥P)).mp
      (by simpa [y, QuotientGroup.mk'_apply] using hy1)
  exact Subgroup.mem_subgroupOf.mp hmem

theorem pElementSubgroup_two_map_inf_le [Finite X] {C L B S : Subgroup X} [C.Normal]
    (hCL : C ≤ Subgroup.normalizer (L : Set X)) (hSB : S ≤ Subgroup.normalizer (B : Set X))
    (hS : IsSylowTwoOf S L) :
    pElementSubgroup 2 (L.map (QuotientGroup.mk' C) ⊓
        (Subgroup.normalizer (B : Set X)).map (QuotientGroup.mk' C)) ≤
      (L ⊓ Subgroup.normalizer (B : Set X)).map (QuotientGroup.mk' C) := by
  set NB : Subgroup X := Subgroup.normalizer (B : Set X) with hNB
  set H : Subgroup X := L ⊓ NB with hH
  set P : Subgroup X := L ⊓ (NB ⊔ C) with hP
  set M : Subgroup X := (P ⊓ NB) ⊔ (P ⊓ C) with hM
  set φ : X →* X ⧸ C := QuotientGroup.mk' C with hφ
  have hCP : C ≤ Subgroup.normalizer (P : Set X) := by
    refine Subgroup.le_normalizer_iff.mpr fun c hc z hz => ?_
    obtain ⟨hzL, hzN⟩ := Subgroup.mem_inf.mp hz
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp (hCL hc) z).mp hzL,
        (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (H := NB ⊔ C)
          (Subgroup.mem_sup_right (S := NB) (T := C) hc)) z).mp hzN⟩
  have hPB : P ≤ NB ⊔ C := inf_le_right
  have hSP : S ≤ P := le_inf hS.1 (hSB.trans le_sup_left)
  have hSylowSP : IsSylowTwoOf S P := by
    refine ⟨hSP, hS.2.1, ?_⟩
    intro h2
    apply hS.2.2
    have hdvd : S.relIndex P ∣ S.relIndex L :=
      ⟨P.relIndex L, (Subgroup.relIndex_mul_relIndex S P L hSP inf_le_left).symm⟩
    exact h2.trans hdvd
  have hMP : M ≤ P := sup_le inf_le_left inf_le_left
  have hSM : S ≤ M := le_sup_of_le_left (le_inf hSP hSB)
  have hMnorm : (M.subgroupOf P).Normal := sup_inf_subgroupOf_normal hCP hPB
  have hModd : ¬ 2 ∣ (M.subgroupOf P).index :=
    not_two_dvd_index_of_isSylowTwoOf_le hSM hSylowSP hMP
  have hPNB : P.map φ ≤ NB.map φ := by
    intro y hy
    obtain ⟨p, hpP, hpy⟩ := Subgroup.mem_map.mp hy
    obtain ⟨-, hpN⟩ := Subgroup.mem_inf.mp hpP
    obtain ⟨n, hnB, c, hcC, hnc⟩ : ∃ n ∈ NB, ∃ c ∈ C, n * c = p := by
      have h := hPB hpP
      rwa [Subgroup.mem_sup_of_normal_right] at h
    refine Subgroup.mem_map.mpr ⟨n, hnB, ?_⟩
    have hc : c ∈ φ.ker := by
      rw [hφ, QuotientGroup.ker_mk']
      exact hcC
    rw [← hpy, ← hnc, map_mul, MonoidHom.mem_ker.mp hc, mul_one]
  have hmapP : P.map φ = L.map φ ⊓ NB.map φ := by
    refine le_antisymm (le_inf (Subgroup.map_mono inf_le_left) hPNB) ?_
    intro y hy
    obtain ⟨hyL, hyB⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨l, hlL, hly⟩ := Subgroup.mem_map.mp hyL
    obtain ⟨n, hnB, hny⟩ := Subgroup.mem_map.mp hyB
    have hc : l⁻¹ * n ∈ C := by
      have hln : (QuotientGroup.mk' C) l = (QuotientGroup.mk' C) n := by
        rw [hφ] at hly hny
        exact hly.trans hny.symm
      exact (QuotientGroup.eq (s := C)).mp (by simpa only [QuotientGroup.mk'_apply] using hln)
    have hl : l = n * (l⁻¹ * n)⁻¹ := by group
    have hlP : l ∈ P := by
      refine Subgroup.mem_inf.mpr ⟨hlL, ?_⟩
      rw [hl]
      exact Subgroup.mul_mem_sup hnB (C.inv_mem hc)
    exact Subgroup.mem_map.mpr ⟨l, hlP, hly⟩
  let ψ : ↥P →* ↥(P.map φ) :=
    (φ.comp P.subtype).codRestrict (P.map φ) fun x => Subgroup.mem_map_of_mem φ x.2
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hxP, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hxP⟩, Subtype.ext (by simpa [ψ] using hxy)⟩
  have hψker : ψ.ker ≤ M.subgroupOf P := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxC : (x : X) ∈ C := by
      have h1 : φ (x : X) = 1 := by
        have h2 := congrArg Subtype.val hx
        simpa [ψ] using h2
      have h2 : (x : X) ∈ φ.ker := MonoidHom.mem_ker.mpr h1
      rwa [hφ, QuotientGroup.ker_mk'] at h2
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨x.2, hxC⟩)
  have hindex : ((M.subgroupOf P).map ψ).index = (M.subgroupOf P).index :=
    Subgroup.index_map_eq (M.subgroupOf P) hψsurj hψker
  have hmapψ : (M.subgroupOf P).map ψ = (M.map φ).subgroupOf (P.map φ) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hxM, hxψ⟩ := Subgroup.mem_map.mp hy
      have hxM' : (x : X) ∈ M := Subgroup.mem_subgroupOf.mp hxM
      have hxP : (x : X) ∈ P := hMP hxM'
      rw [Subgroup.mem_subgroupOf]
      have hyv : ((y : ↥(P.map φ)) : X ⧸ C) = φ (x : X) := by
        have h2 := congrArg Subtype.val hxψ
        simpa [ψ] using h2.symm
      rw [hyv]
      exact Subgroup.mem_map_of_mem φ hxM'
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy
      obtain ⟨m, hmM, hm⟩ := Subgroup.mem_map.mp hy
      have hmP : m ∈ P := hMP hmM
      exact Subgroup.mem_map.mpr ⟨⟨m, hmP⟩, Subgroup.mem_subgroupOf.mpr hmM,
        Subtype.ext (by simpa [ψ] using hm)⟩
  have hN'norm : ((M.map φ).subgroupOf (P.map φ)).Normal := by
    rw [← hmapψ]
    exact hMnorm.map ψ hψsurj
  have hN'odd : ¬ 2 ∣ ((M.map φ).subgroupOf (P.map φ)).index := by
    rw [← hmapψ, hindex]
    exact hModd
  have hmain : pElementSubgroup 2 (P.map φ) ≤ M.map φ :=
    pElementSubgroup_two_le_of_odd_index (Subgroup.map_mono hMP) hN'norm hN'odd
  have hPeq : P ⊓ NB = H := by
    rw [hP, hH]
    ext z
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, Subgroup.mem_sup_left h.2⟩, h.2⟩⟩
  have hbot : (P ⊓ C).map φ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro z hz
    have hzC : z ∈ C := (Subgroup.mem_inf.mp hz).2
    have h1 : z ∈ φ.ker := by
      rw [hφ, QuotientGroup.ker_mk']
      exact hzC
    exact h1
  have hMH : M.map φ ≤ H.map φ := by
    have heq : M.map φ = H.map φ := by
      calc M.map φ = ((P ⊓ NB) ⊔ (P ⊓ C)).map φ := by rw [hM]
        _ = (P ⊓ NB).map φ ⊔ (P ⊓ C).map φ := Subgroup.map_sup _ _ _
        _ = H.map φ := by rw [hbot, hPeq, sup_bot_eq]
    rw [heq]
  rw [← hmapP]
  exact hmain.trans hMH

theorem pElementSubgroup_two_eq_of_perfect [Finite X] {L : Subgroup X} (hL : ⁅L, L⁆ = L) :
    pElementSubgroup 2 L = L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWL : pElementSubgroup 2 L ≤ L := pElementSubgroup_le L
  have hconj : ∀ l ∈ L, ∀ x ∈ pElementSubgroup 2 L, l * x * l⁻¹ ∈ pElementSubgroup 2 L :=
    fun l hl _ hx => conj_mem_pElementSubgroup_two hl hx
  have hWnorm : ((pElementSubgroup 2 L).subgroupOf L).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hWL).mpr ?_
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨hconj l hl x, fun hx => by
      have h1 := hconj l⁻¹ (L.inv_mem hl) (l * x * l⁻¹) hx
      rwa [show l⁻¹ * (l * x * l⁻¹) * (l⁻¹)⁻¹ = x by group] at h1⟩
  have hodd : Odd ((pElementSubgroup 2 L).subgroupOf L).index := by
    obtain ⟨S⟩ : Nonempty (Sylow 2 ↥L) := Sylow.nonempty
    have hSle : (S : Subgroup ↥L) ≤ (pElementSubgroup 2 L).subgroupOf L := by
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      unfold pElementSubgroup
      refine Subgroup.subset_closure ⟨x.2, ?_⟩
      obtain ⟨n, hn⟩ := S.isPGroup' ⟨x, hx⟩
      have h1 : (x : ↥L) ^ 2 ^ n = 1 := congrArg Subtype.val hn
      obtain ⟨k, -, hk⟩ :=
        (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one (congrArg Subtype.val h1))
      exact ⟨k, hk⟩
    have hdvd : ((pElementSubgroup 2 L).subgroupOf L).index ∣ (S : Subgroup ↥L).index :=
      Subgroup.index_dvd_of_le hSle
    have hnd : ¬ 2 ∣ (S : Subgroup ↥L).index := S.not_dvd_index
    exact Nat.not_even_iff_odd.mp (by
      rw [even_iff_two_dvd]
      exact fun h => hnd (h.trans hdvd))
  refine le_antisymm hWL ?_
  haveI : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL
  have htop : (pElementSubgroup 2 L).subgroupOf L = ⊤ := by
    have hperf : Group.IsPerfect (↥L ⧸ (pElementSubgroup 2 L).subgroupOf L) :=
      Group.IsPerfect.ofSurjective
        (f := QuotientGroup.mk' ((pElementSubgroup 2 L).subgroupOf L))
        (QuotientGroup.mk'_surjective _)
    by_contra hne
    haveI : Nontrivial (↥L ⧸ (pElementSubgroup 2 L).subgroupOf L) :=
      QuotientGroup.nontrivial_iff.mpr hne
    have hsolv : Group.IsSolvable (↥L ⧸ (pElementSubgroup 2 L).subgroupOf L) :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ (by rwa [Subgroup.index_eq_card] at hodd)
    exact Group.IsPerfect.not_isSolvable _ hsolv
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥L) ∈ (pElementSubgroup 2 L).subgroupOf L :=
    htop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp hmem

theorem le_of_le_sup_of_perfect {L H C : Subgroup X} [C.Normal] (hHL : H ≤ L)
    (hL : ⁅L, L⁆ = L) (hLC : ⁅L, L ⊓ C⁆ ≤ H) (hsup : L ≤ H ⊔ C) : L ≤ H := by
  have hdecomp : ∀ l ∈ L, ∃ h ∈ H, ∃ d ∈ L ⊓ C, h * d = l := by
    intro l hl
    obtain ⟨h, hhH, c, hcC, hc⟩ : ∃ h ∈ H, ∃ c ∈ C, h * c = l := by
      have h := hsup hl
      rwa [Subgroup.mem_sup_of_normal_right] at h
    have hdl : h⁻¹ * l = c := by rw [← hc]; group
    refine ⟨h, hhH, h⁻¹ * l, ⟨L.mul_mem (L.inv_mem (hHL hhH)) hl, ?_⟩, ?_⟩
    · rw [hdl]
      exact hcC
    · rw [← hc]
      group
  have hconj : ∀ l ∈ L, ∀ x ∈ H, l * x * l⁻¹ ∈ H := by
    intro l hl x hx
    obtain ⟨h, hhH, d, hd, hdl⟩ := hdecomp l hl
    have hdx : d * x * d⁻¹ ∈ H := by
      have hcomm : ⁅x⁻¹, d⁆ ∈ H :=
        hLC (Subgroup.commutator_mem_commutator (H₁ := L) (H₂ := L ⊓ C)
          (L.inv_mem (hHL hx)) hd)
      have hdx' : d * x * d⁻¹ = x * ⁅x⁻¹, d⁆ := by
        simp only [commutatorElement_def]
        group
      rw [hdx']
      exact H.mul_mem hx hcomm
    have hlx : l * x * l⁻¹ = h * (d * x * d⁻¹) * h⁻¹ := by rw [← hdl]; group
    rw [hlx]
    exact H.mul_mem (H.mul_mem hhH hdx) (H.inv_mem hhH)
  have hLH : L ≤ Subgroup.normalizer (H : Set X) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨hconj l hl x, fun hx => by
      have h1 := hconj l⁻¹ (L.inv_mem hl) (l * x * l⁻¹) hx
      rwa [show l⁻¹ * (l * x * l⁻¹) * (l⁻¹)⁻¹ = x by group] at h1⟩
  rw [← hL]
  refine (Subgroup.commutator_le).mpr fun l₁ hl₁ l₂ hl₂ => ?_
  obtain ⟨h, hhH, d, hd, hdl⟩ := hdecomp l₁ hl₁
  have hmem1 : ⁅d, l₂⁆ ∈ H := by
    have h1 : ⁅l₂, d⁆ ∈ ⁅L, L ⊓ C⁆ := Subgroup.commutator_mem_commutator hl₂ hd
    have h2 : ⁅d, l₂⁆ = ⁅l₂, d⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h2]
    exact hLC (Subgroup.inv_mem (⁅L, L ⊓ C⁆) h1)
  have hmem2 : l₂ * h⁻¹ * l₂⁻¹ ∈ H :=
    (Subgroup.mem_normalizer_iff.mp (hLH hl₂) h⁻¹).mp (H.inv_mem hhH)
  have hform : ⁅l₁, l₂⁆ = h * ⁅d, l₂⁆ * (l₂ * h⁻¹ * l₂⁻¹) := by
    rw [← hdl]
    simp only [commutatorElement_def]
    group
  rw [hform]
  exact H.mul_mem (H.mul_mem hhH hmem1) hmem2

theorem three_dvd_card_of_mem_map [Finite X] {Y : Type*} [Group Y] (f : X →* Y) {H : Subgroup X}
    {y : Y} (hy : y ∈ H.map f) (ho : orderOf y = 3) : 3 ∣ Nat.card H := by
  have h1 : orderOf y ∣ Nat.card ↥(H.map f) := Subgroup.orderOf_dvd_natCard (H.map f) hy
  rw [ho] at h1
  exact h1.trans (Subgroup.card_map_dvd H f)

end CFSG.LocalAnalysis.RankThreeTheoremC.FiveTwentySix
