module

public import CFSG.Quasithin.Background.C116Two.Ctx
public import CFSG.Quasithin.Background.C1PackC19
public import CFSG.Quasithin.Background.C2Aux

public section

namespace CFSG.QuasithinUnique.L246C127.Deg

open CFSG.Quasithin.C116Two CFSG.QuasithinUnique CFSG.Quasithin CFSG.Open
open scoped commutatorElement

section

lemma conj_eq_of_rel {G : Type} [Group G] (m a s k w : G) (hk : k * w * k⁻¹ = w)
    (hpk : m * a = s * k) : m * (a * w * a⁻¹) * m⁻¹ = s * w * s⁻¹ := by
  calc m * (a * w * a⁻¹) * m⁻¹ = (m * a) * w * (m * a)⁻¹ := by group
    _ = (s * k) * w * (s * k)⁻¹ := by rw [hpk]
    _ = s * (k * w * k⁻¹) * s⁻¹ := by group
    _ = s * w * s⁻¹ := by rw [hk]

theorem transversal_inj {G : Type} [Group G] (M K₀ : Subgroup G)
    (r : (↥M ⧸ K₀.subgroupOf M) → ↥M)
    (hr : ∀ q, (QuotientGroup.mk (r q) : ↥M ⧸ K₀.subgroupOf M) = q) :
    ∀ q q', ((r q)⁻¹ * (r q') : ↥M) ∈ K₀.subgroupOf M → q = q' := by
  intro q q' h
  have h2 : (QuotientGroup.mk (r q) : ↥M ⧸ K₀.subgroupOf M) = QuotientGroup.mk (r q') :=
    QuotientGroup.eq.mpr h
  exact (hr q).symm.trans (h2.trans (hr q'))

theorem exists_norm_fixed {G : Type} [Group G] (M W K₀ : Subgroup G) [Finite M]
    [Fintype (↥M ⧸ K₀.subgroupOf M)]
    (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hMW : ∀ m ∈ M, ∀ w ∈ W, m * w * m⁻¹ ∈ W) (hK₀M : K₀ ≤ M)
    (r : (↥M ⧸ K₀.subgroupOf M) → ↥M)
    (hr : ∀ q, (QuotientGroup.mk (r q) : ↥M ⧸ K₀.subgroupOf M) = q)
    (w : G) (hw : w ∈ W)
    (hfix : ∀ k ∈ K₀, k * w * k⁻¹ = w) :
    ∃ (hmem : ∀ q, ((r q : G) * w * (r q : G)⁻¹) ∈ W) (u : ↥W),
      (∀ m ∈ M, m * (u : G) * m⁻¹ = (u : G)) ∧
      (∀ C : Subgroup G, (∀ m ∈ M, m ∉ K₀ → m * w * m⁻¹ ∈ C) → (u : G) * w⁻¹ ∈ C) ∧
      (∀ {V' : Type} [CommGroup V'] (ψ : ↥W →* V'),
        ψ u = ∏ q, ψ ⟨(r q : G) * w * (r q : G)⁻¹, hmem q⟩) := by
  classical
  letI : CommGroup ↥W :=
    { (inferInstance : Group ↥W) with
      mul_comm := fun a b => Subtype.ext (hW (a : G) a.2 (b : G) b.2) }
  have hmem : ∀ q, ((r q : G) * w * (r q : G)⁻¹) ∈ W :=
    fun q => hMW (r q : G) (r q).2 w hw
  obtain ⟨c, hc⟩ : ∃ c : (↥M ⧸ K₀.subgroupOf M) → ↥W,
      ∀ q, (c q : G) = (r q : G) * w * (r q : G)⁻¹ :=
    ⟨fun q => ⟨(r q : G) * w * (r q : G)⁻¹, hmem q⟩, fun q => rfl⟩
  have hcq : ∀ q, c q = ⟨(r q : G) * w * (r q : G)⁻¹, hmem q⟩ :=
    fun q => Subtype.ext (hc q)
  have htrans : ∀ q q', ((r q)⁻¹ * (r q') : ↥M) ∈ K₀.subgroupOf M → q = q' :=
    transversal_inj M K₀ r hr
  have hinv : ∀ m ∈ M, m * ((∏ q, c q : ↥W) : G) * m⁻¹ = ((∏ q, c q : ↥W) : G) := by
    intro m hm
    obtain ⟨cj, hcj⟩ : ∃ cj : ↥W →* ↥W, ∀ x : ↥W, ((cj x : ↥W) : G) = m * (x : G) * m⁻¹ :=
      ⟨MonoidHom.mk' (fun x : ↥W => (⟨m * (x : G) * m⁻¹, hMW m hm (x : G) x.2⟩ : ↥W))
        (fun x y => Subtype.ext (by simp [mul_assoc])), fun x => rfl⟩
    obtain ⟨e, he⟩ : ∃ e : (↥M ⧸ K₀.subgroupOf M) → (↥M ⧸ K₀.subgroupOf M),
        ∀ q, e q = QuotientGroup.mk ((⟨m, hm⟩ : ↥M) * r q) :=
      ⟨fun q => QuotientGroup.mk ((⟨m, hm⟩ : ↥M) * r q), fun q => rfl⟩
    have he_inj : Function.Injective e := by
      intro q q' hqq
      have hqq' : (QuotientGroup.mk ((⟨m, hm⟩ : ↥M) * r q) : ↥M ⧸ K₀.subgroupOf M)
          = QuotientGroup.mk ((⟨m, hm⟩ : ↥M) * r q') :=
        (he q).symm.trans (hqq.trans (he q'))
      have h1 := QuotientGroup.eq.mp hqq'
      apply htrans q q'
      have h2 : (r q)⁻¹ * r q' = ((⟨m, hm⟩ : ↥M) * r q)⁻¹ * ((⟨m, hm⟩ : ↥M) * r q') := by
        group
      rw [h2]
      exact h1
    have he_bij : Function.Bijective e := Finite.injective_iff_bijective.mp he_inj
    have hperm : ∀ q, cj (c q) = c (e q) := by
      intro q
      apply Subtype.ext
      rw [hcj, hc q, hc (e q)]
      have hrel : (QuotientGroup.mk (r (e q)) : ↥M ⧸ K₀.subgroupOf M)
          = QuotientGroup.mk ((⟨m, hm⟩ : ↥M) * r q) :=
        (hr (e q)).trans (he q)
      have hk1 : (r (e q))⁻¹ * ((⟨m, hm⟩ : ↥M) * r q) ∈ K₀.subgroupOf M :=
        QuotientGroup.eq.mp hrel
      have hk2 : ((r (e q) : G))⁻¹ * (m * (r q : G)) ∈ K₀ :=
        Subgroup.mem_subgroupOf.mp hk1
      have hpk : m * (r q : G) = (r (e q) : G) * ((r (e q) : G)⁻¹ * (m * (r q : G))) :=
        (mul_inv_cancel_left _ _).symm
      exact conj_eq_of_rel m (r q : G) (r (e q) : G) _ w (hfix _ hk2) hpk
    have hprod : cj (∏ q, c q) = ∏ q, c q := by
      rw [map_prod]
      exact Fintype.prod_bijective e he_bij (fun q => cj (c q)) c hperm
    have h2 := congrArg Subtype.val hprod
    rw [hcj] at h2
    exact h2
  have hC : ∀ C : Subgroup G, (∀ m ∈ M, m ∉ K₀ → m * w * m⁻¹ ∈ C) →
      ((∏ q, c q : ↥W) : G) * w⁻¹ ∈ C := by
    intro C hCm
    obtain ⟨q₀, hq₀⟩ : ∃ q₀ : ↥M ⧸ K₀.subgroupOf M, q₀ = QuotientGroup.mk (1 : ↥M) :=
      ⟨_, rfl⟩
    have hr₀ : (r q₀ : G) ∈ K₀ := by
      have hmq₀ : (QuotientGroup.mk (r q₀) : ↥M ⧸ K₀.subgroupOf M)
          = QuotientGroup.mk (1 : ↥M) :=
        (hr q₀).trans hq₀
      have h1 : (r q₀)⁻¹ * (1 : ↥M) ∈ K₀.subgroupOf M := QuotientGroup.eq.mp hmq₀
      have h2 := Subgroup.mem_subgroupOf.mp h1
      simpa using h2
    have hcq₀ : (c q₀ : G) = w := by
      rw [hc q₀]
      exact hfix _ hr₀
    obtain ⟨P, hP⟩ : ∃ P : ↥W, P = ∏ q ∈ Finset.univ.erase q₀, c q := ⟨_, rfl⟩
    have hsplit : (∏ q, c q : ↥W) = c q₀ * P := by
      rw [hP]
      exact (Finset.mul_prod_erase Finset.univ c (Finset.mem_univ q₀)).symm
    have hPC : P ∈ C.subgroupOf W := by
      rw [hP]
      apply Subgroup.prod_mem
      intro q hq
      have hne : q ≠ q₀ := Finset.ne_of_mem_erase hq
      have hK : (r q : G) ∉ K₀ := by
        intro hK
        apply hne
        have hH : (r q)⁻¹ * (1 : ↥M) ∈ K₀.subgroupOf M := by
          rw [Subgroup.mem_subgroupOf]
          simpa using K₀.inv_mem hK
        have hmq : (QuotientGroup.mk (r q) : ↥M ⧸ K₀.subgroupOf M)
            = QuotientGroup.mk (1 : ↥M) :=
          QuotientGroup.eq.mpr hH
        rw [hq₀]
        exact (hr q).symm.trans hmq
      rw [Subgroup.mem_subgroupOf, hc q]
      exact hCm _ (r q).2 hK
    have hcomm : w * (P : G) = (P : G) * w := hW w hw (P : G) P.2
    have key : ((∏ q, c q : ↥W) : G) * w⁻¹ = (P : G) := by
      rw [hsplit]
      show (c q₀ : G) * (P : G) * w⁻¹ = (P : G)
      rw [hcq₀, hcomm, mul_inv_cancel_right]
    rw [key]
    exact Subgroup.mem_subgroupOf.mp hPC
  have hψ : ∀ {V' : Type} [CommGroup V'] (ψ : ↥W →* V'),
      ψ (∏ q, c q) = ∏ q, ψ ⟨(r q : G) * w * (r q : G)⁻¹, hmem q⟩ := by
    intro V' _ ψ
    rw [map_prod]
    exact Finset.prod_congr rfl (fun q _ => congrArg ψ (hcq q))
  exact ⟨hmem, ∏ q, c q, hinv, hC, hψ⟩

end

section

theorem fh7_normalizer_of_conj_eq {G : Type} [Group G] {K : Subgroup G} {s : G}
    (h : conjByElt s K = K) : s ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  change x ∈ K ↔ s * x * s⁻¹ ∈ K
  have e : s⁻¹ * (s * x * s⁻¹) * s = x := by group
  constructor
  · intro hx
    have hmem : s * x * s⁻¹ ∈ conjByElt s K := by
      rw [mem_conjByElt, e]
      exact hx
    rw [h] at hmem
    exact hmem
  · intro hx
    have hmem : s * x * s⁻¹ ∈ conjByElt s K := by
      rw [h]
      exact hx
    rw [mem_conjByElt, e] at hmem
    exact hmem

theorem fh7_inv_mul_normalizer {G : Type} [Group G] {K : Subgroup G} {s t : G}
    (h : conjByElt s K = conjByElt t K) : s⁻¹ * t ∈ Subgroup.normalizer (K : Set G) := by
  have hy : ∀ y : G, s⁻¹ * y * s ∈ K ↔ t⁻¹ * y * t ∈ K := by
    intro y
    have hy' : y ∈ conjByElt s K ↔ y ∈ conjByElt t K := by rw [h]
    rw [mem_conjByElt, mem_conjByElt] at hy'
    exact hy'
  rw [Subgroup.mem_normalizer_iff]
  intro x
  change x ∈ K ↔ s⁻¹ * t * x * (s⁻¹ * t)⁻¹ ∈ K
  have e1 : s⁻¹ * t * x * (s⁻¹ * t)⁻¹ = s⁻¹ * (t * x * t⁻¹) * s := by group
  have e2 : t⁻¹ * (t * x * t⁻¹) * t = x := by group
  have h2 := hy (t * x * t⁻¹)
  rw [e2] at h2
  rw [e1]
  exact h2.symm

theorem fh7_mul_comm_of_comm_eq_bot {G : Type} [Group G] {A B : Subgroup G}
    (hAB : ⁅A, B⁆ = ⊥) {a b : G} (ha : a ∈ A) (hb : b ∈ B) : a * b = b * a := by
  have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAB ha
  exact (Subgroup.mem_centralizer_iff.mp h1 b hb).symm

theorem fh7_conj_comm {G : Type} [Group G] [Finite G] {P T K : Subgroup G}
    (hP : CharTwo P) (hTP : T ≤ P) (hKP : IsBlock2 P K) {u : G} (huK : u ∈ K)
    (hfix : ∀ x ∈ T ⊓ Subgroup.normalizer (K : Set G), x * u * x⁻¹ = u)
    {t t' : G} (ht : t ∈ T) (ht' : t' ∈ T) :
    (t * u * t⁻¹) * (t' * u * t'⁻¹) = (t' * u * t'⁻¹) * (t * u * t⁻¹) := by
  by_cases h : conjByElt t K = conjByElt t' K
  · have hs : t⁻¹ * t' ∈ T ⊓ Subgroup.normalizer (K : Set G) :=
      Subgroup.mem_inf.mpr ⟨T.mul_mem (T.inv_mem ht) ht', fh7_inv_mul_normalizer h⟩
    have hfs := hfix _ hs
    have e : t' * u * t'⁻¹ = t * u * t⁻¹ := by
      calc t' * u * t'⁻¹ = t * ((t⁻¹ * t') * u * (t⁻¹ * t')⁻¹) * t⁻¹ := by group
        _ = t * u * t⁻¹ := by rw [hfs]
    rw [e]
  · have hB1 : IsBlock2 P (conjByElt t K) := IsBlock2.conjByElt_of_mem hKP (hTP ht)
    have hB2 : IsBlock2 P (conjByElt t' K) := IsBlock2.conjByElt_of_mem hKP (hTP ht')
    have hcomm := distinctBlocksCommuteStatement P (conjByElt t K) (conjByElt t' K) hP hB1 hB2 h
    have hx : t * u * t⁻¹ ∈ conjByElt t K := by
      rw [mem_conjByElt]
      have e : t⁻¹ * (t * u * t⁻¹) * t = u := by group
      rw [e]
      exact huK
    have hy : t' * u * t'⁻¹ ∈ conjByElt t' K := by
      rw [mem_conjByElt]
      have e : t'⁻¹ * (t' * u * t'⁻¹) * t' = u := by group
      rw [e]
      exact huK
    exact fh7_mul_comm_of_comm_eq_bot hcomm hx hy

theorem fh7_closure_comm {G : Type} [Group G] {S : Set G}
    (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a := by
  have hc : Subgroup.closure S ≤ Subgroup.centralizer S := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    show x ∈ Subgroup.centralizer S
    exact Subgroup.mem_centralizer_iff.mpr (fun h hh => hS h hh x hx)
  intro a ha b hb
  have hab : Subgroup.closure S ≤ Subgroup.centralizer ({a} : Set G) := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    show x ∈ Subgroup.centralizer ({a} : Set G)
    apply Subgroup.mem_centralizer_iff.mpr
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (Subgroup.mem_centralizer_iff.mp (hc ha) x hx).symm
  exact Subgroup.mem_centralizer_iff.mp (hab hb) a (Set.mem_singleton a)

theorem fh7_closure_sq {G : Type} [Group G] {S : Set G}
    (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hS2 : ∀ x ∈ S, x ^ 2 = 1) :
    ∀ a ∈ Subgroup.closure S, a ^ 2 = 1 := by
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hS2 x hx
  | one => simp
  | mul x y hx hy hxs hys =>
    have hcomm : Commute x y := fh7_closure_comm hS x hx y hy
    rw [hcomm.mul_pow, hxs, hys, one_mul]
  | inv x hx hxs =>
    rw [inv_pow, hxs, inv_one]

theorem fh7_closure_conj {G : Type} [Group G] {S : Set G} {m : G}
    (hm : ∀ x ∈ S, m * x * m⁻¹ ∈ Subgroup.closure S) :
    ∀ w ∈ Subgroup.closure S, m * w * m⁻¹ ∈ Subgroup.closure S := by
  have hle : Subgroup.closure S ≤ (Subgroup.closure S).comap (MulAut.conj m).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    show x ∈ (Subgroup.closure S).comap (MulAut.conj m).toMonoidHom
    rw [Subgroup.mem_comap]
    exact hm x hx
  intro w hw
  exact Subgroup.mem_comap.mp (hle hw)

theorem exists_central_not_centralized {G : Type} [Group G] [Finite G] {P T K : Subgroup G}
    (hP : CharTwo P) (hT2 : IsPGroup 2 T) (hTP : T ≤ P) (hKP : IsBlock2 P K)
    (hUT : blockU K ≤ T) {u : G} (hu : u ∈ blockU K) (huZ : u ∉ blockZ K)
    (hfix : ∀ x ∈ T ⊓ Subgroup.normalizer (K : Set G), x * u * x⁻¹ = u) :
    ∃ z ∈ quasithinOmegaOneCenter T, ∃ k ∈ K, z * k ≠ k * z := by
  classical
  have huK : u ∈ K :=
    CFSG.QuasithinUnique.C1.blockQ_le K (CFSG.QuasithinUnique.C1.blockU_le_blockQ hKP.1 hu)
  have huT : u ∈ T := hUT hu
  have hu2 : u ^ 2 = 1 := CFSG.QuasithinUnique.C1.blockU_sq hKP.1 u hu
  have huu : u * u = 1 := (sq u).symm.trans hu2
  obtain ⟨S, hSdef⟩ : ∃ S : Set G, S = {x | ∃ t ∈ T, x = t * u * t⁻¹} := ⟨_, rfl⟩
  have hmemS : ∀ x, x ∈ S ↔ ∃ t ∈ T, x = t * u * t⁻¹ := by
    intro x
    subst hSdef
    exact Iff.rfl
  have hScomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    obtain ⟨t, ht, rfl⟩ := (hmemS x).mp hx
    obtain ⟨t', ht', rfl⟩ := (hmemS y).mp hy
    exact fh7_conj_comm hP hTP hKP huK hfix ht ht'
  have hSsq : ∀ x ∈ S, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := (hmemS x).mp hx
    rw [sq]
    calc t * u * t⁻¹ * (t * u * t⁻¹) = t * (u * u) * t⁻¹ := by group
      _ = 1 := by simp [huu]
  have hST : ∀ x ∈ S, x ∈ T := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := (hmemS x).mp hx
    exact T.mul_mem (T.mul_mem ht huT) (T.inv_mem ht)
  have hSconj : ∀ m ∈ T, ∀ x ∈ S, m * x * m⁻¹ ∈ S := by
    intro m hm x hx
    obtain ⟨t, ht, rfl⟩ := (hmemS x).mp hx
    rw [hmemS]
    exact ⟨m * t, T.mul_mem hm ht, by group⟩
  have huS : u ∈ S := (hmemS u).mpr ⟨1, T.one_mem, by simp⟩
  have hW : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a :=
    fh7_closure_comm hScomm
  have hWT : Subgroup.closure S ≤ T := (Subgroup.closure_le _).mpr hST
  have hWsq : ∀ a ∈ Subgroup.closure S, a ^ 2 = 1 := fh7_closure_sq hScomm hSsq
  have hMW : ∀ m ∈ T, ∀ w ∈ Subgroup.closure S, m * w * m⁻¹ ∈ Subgroup.closure S :=
    fun m hm => fh7_closure_conj (fun x hx => Subgroup.subset_closure (hSconj m hm x hx))
  have hw : u ∈ Subgroup.closure S := Subgroup.subset_closure huS
  have hK₀M : T ⊓ Subgroup.normalizer (K : Set G) ≤ T := inf_le_left
  haveI : Finite (↥T ⧸ (T ⊓ Subgroup.normalizer (K : Set G)).subgroupOf T) := inferInstance
  haveI : Fintype (↥T ⧸ (T ⊓ Subgroup.normalizer (K : Set G)).subgroupOf T) :=
    Fintype.ofFinite _
  obtain ⟨r, hr⟩ : ∃ r : (↥T ⧸ (T ⊓ Subgroup.normalizer (K : Set G)).subgroupOf T) → ↥T,
      ∀ q, (QuotientGroup.mk (r q) : ↥T ⧸ (T ⊓ Subgroup.normalizer (K : Set G)).subgroupOf T) = q :=
    ⟨fun q => Classical.choose (QuotientGroup.mk_surjective q),
      fun q => Classical.choose_spec (QuotientGroup.mk_surjective q)⟩
  obtain ⟨_, z', hz'inv, hz'C, _⟩ := exists_norm_fixed T (Subgroup.closure S)
    (T ⊓ Subgroup.normalizer (K : Set G)) hW hMW hK₀M r hr u hw hfix
  have hzT : (z' : G) ∈ T := hWT z'.2
  have hzC : (z' : G) ∈ Subgroup.centralizer (T : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun h hh => mul_inv_eq_iff_eq_mul.mp (hz'inv h hh))
  have hzQ : (z' : G) ^ 2 = 1 := hWsq _ z'.2
  have hzmem : (z' : G) ∈ quasithinOmegaOneCenter T := by
    unfold quasithinOmegaOneCenter
    refine Subgroup.subset_closure ?_
    rw [Set.mem_setOf_eq]
    exact ⟨Subgroup.mem_inf.mpr ⟨hzT, hzC⟩, hzQ⟩
  have hCclause : ∀ m ∈ T, m ∉ T ⊓ Subgroup.normalizer (K : Set G) →
      m * u * m⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
    intro m hm hmN
    have hmnorm : m ∉ Subgroup.normalizer (K : Set G) :=
      fun h => hmN (Subgroup.mem_inf.mpr ⟨hm, h⟩)
    have hne : conjByElt m K ≠ K := fun h => hmnorm (fh7_normalizer_of_conj_eq h)
    have hcomm := distinctBlocksCommuteStatement P (conjByElt m K) K hP
      (IsBlock2.conjByElt_of_mem hKP (hTP hm)) hKP hne
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hx : m * u * m⁻¹ ∈ conjByElt m K := by
      rw [mem_conjByElt]
      have e : m⁻¹ * (m * u * m⁻¹) * m = u := by group
      rw [e]
      exact huK
    exact hle hx
  have hcK : (z' : G) * u⁻¹ ∈ Subgroup.centralizer (K : Set G) := hz'C _ hCclause
  have hkex : ∃ k ∈ K, k * u ≠ u * k := by
    by_contra hcon
    apply huZ
    show u ∈ blockU K ⊓ Subgroup.centralizer (K : Set G)
    refine Subgroup.mem_inf.mpr ⟨hu, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro k hk
    by_contra hne
    exact hcon ⟨k, hk, hne⟩
  obtain ⟨k, hkK, hku⟩ := hkex
  refine ⟨(z' : G), hzmem, k, hkK, ?_⟩
  intro hzk
  have hck : k * ((z' : G) * u⁻¹) = ((z' : G) * u⁻¹) * k :=
    Subgroup.mem_centralizer_iff.mp hcK k hkK
  apply hku
  have key : ((z' : G) * u⁻¹) * (u * k) = ((z' : G) * u⁻¹) * (k * u) := by
    calc ((z' : G) * u⁻¹) * (u * k) = (z' : G) * k := by group
      _ = k * (z' : G) := hzk
      _ = k * ((z' : G) * u⁻¹) * u := by group
      _ = ((z' : G) * u⁻¹) * k * u := by rw [hck]
      _ = ((z' : G) * u⁻¹) * (k * u) := by group
  exact (mul_left_cancel key).symm

end

end CFSG.QuasithinUnique.L246C127.Deg
