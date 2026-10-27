module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecW
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupMap

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace B5a

section OddTwo

variable {A A' : Type*} [Group A] [Group A'] [Finite A] [Finite A']

omit [Finite A] [Finite A'] in
theorem le_oddTwoCore {M : Subgroup A} (hM : M.Normal)
    (h2 : ∀ m ∈ M, ∃ k : ℕ, m ^ 2 ^ k ∈ pPrimeCore 2 A) : M ≤ oddTwoCore A := by
  intro m hm
  show QuotientGroup.mk' (pPrimeCore 2 A) m ∈ pCore 2 (A ⧸ pPrimeCore 2 A)
  have hn : (M.map (QuotientGroup.mk' (pPrimeCore 2 A))).Normal :=
    hM.map _ (QuotientGroup.mk'_surjective _)
  have hp : IsPGroup 2 (M.map (QuotientGroup.mk' (pPrimeCore 2 A))) := by
    intro g
    obtain ⟨x, hx⟩ := g
    obtain ⟨m', hm', rfl⟩ := mem_map.mp hx
    obtain ⟨k, hk⟩ := h2 m' hm'
    refine ⟨k, Subtype.ext ?_⟩
    rw [SubmonoidClass.coe_pow, ← map_pow, OneMemClass.coe_one, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hk
  have hle : M.map (QuotientGroup.mk' (pPrimeCore 2 A)) ≤ pCore 2 (A ⧸ pPrimeCore 2 A) :=
    le_sSup (show M.map (QuotientGroup.mk' (pPrimeCore 2 A)) ∈
      {K : Subgroup (A ⧸ pPrimeCore 2 A) | K.Normal ∧ IsPGroup 2 K} from ⟨hn, hp⟩)
  exact hle (mem_map_of_mem _ hm)

omit [Finite A] [Finite A'] in
theorem exists_pow_mem_of_mem_oddTwoCore {x : A} (hx : x ∈ oddTwoCore A) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ pPrimeCore 2 A := by
  have hx' : QuotientGroup.mk' (pPrimeCore 2 A) x ∈ pCore 2 (A ⧸ pPrimeCore 2 A) := hx
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup ⟨_, hx'⟩
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
  exact congrArg Subtype.val hk

theorem map_mem_oddTwoCore (f : A →* A') (hf : Function.Surjective f) {x : A}
    (hx : x ∈ oddTwoCore A) : f x ∈ oddTwoCore A' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO := CatalogueBCentralQuotient.primeCore_map_le 2 f hf
  refine le_oddTwoCore (M := (oddTwoCore A).map f) (Normal.map inferInstance f hf) ?_
    (mem_map_of_mem f hx)
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_oddTwoCore hm
  exact ⟨k, by rw [← map_pow]; exact hO (mem_map_of_mem f hk)⟩

omit [Finite A] in
theorem mem_oddTwoCore_of_injective (f : A →* A') (hf : Function.Injective f) {x : A}
    (hx : f x ∈ oddTwoCore A') : x ∈ oddTwoCore A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_oddTwoCore (M := (oddTwoCore A').comap f) (Normal.comap inferInstance f) ?_ hx
  intro m hm
  obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_oddTwoCore (A := A') hm
  refine ⟨k, ?_⟩
  have hn : ((pPrimeCore 2 A').comap f).Normal := Normal.comap inferInstance f
  have hodd : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 A').comap f)) := by
    have h1 : Nat.card ((pPrimeCore 2 A').comap f) ∣ Nat.card (pPrimeCore 2 A') :=
      Subgroup.card_comap_dvd_of_injective _ f hf
    exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
  have hle : (pPrimeCore 2 A').comap f ≤ pPrimeCore 2 A := le_sSup ⟨hn, hodd⟩
  exact hle (show f (m ^ 2 ^ k) ∈ pPrimeCore 2 A' by rw [map_pow]; exact hk)

end OddTwo

section Solvable

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_mem_of_isPerfect' {V N : Subgroup G} [Group.IsPerfect V] (hNV : N ≤ V)
    (hN : (N.subgroupOf V).Normal) {w : G} (hwV : w ∈ normalizer (V : Set G))
    (hA : ∀ v ∈ V, ∀ u ∈ V, ⁅v⁻¹ * w⁻¹ * v * w, u⁆ ∈ N) :
    ∀ v ∈ V, v⁻¹ * w⁻¹ * v * w ∈ N := by
  have hwV' : ∀ v ∈ V, v⁻¹ * w⁻¹ * v * w ∈ V := by
    intro v hv
    have h1 := (mem_normalizer_iff.mp (inv_mem hwV) v).mp hv
    rw [inv_inv] at h1
    rw [show v⁻¹ * w⁻¹ * v * w = v⁻¹ * (w⁻¹ * v * w) by group]
    exact mul_mem (inv_mem hv) h1
  have hNc : ∀ (v : G), v ∈ V → ∀ o ∈ N, v⁻¹ * o * v ∈ N := by
    intro v hv o ho
    have h1 := hN.conj_mem ⟨o, hNV ho⟩ ho ⟨v, hv⟩⁻¹
    rw [mem_subgroupOf] at h1
    simpa only [coe_mul, coe_inv, inv_inv] using h1
  let δ : ↥V → ↥V := fun v => ⟨(v : G)⁻¹ * w⁻¹ * v * w, hwV' v v.2⟩
  have hcen : ∀ u v : ↥V, ((δ u : ↥V) : ↥V ⧸ N.subgroupOf V) * (v : ↥V ⧸ N.subgroupOf V) =
      (v : ↥V ⧸ N.subgroupOf V) * (δ u : ↥V ⧸ N.subgroupOf V) := by
    intro u v
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
    have h1 := hA u u.2 (v : G)⁻¹ (inv_mem v.2)
    have h2 : (((δ u * v)⁻¹ * (v * δ u) : ↥V) : G) = ((δ u : ↥V) : G)⁻¹ *
        ⁅((δ u : ↥V) : G), (v : G)⁻¹⁆ * ((δ u : ↥V) : G) := by
      simp only [coe_mul, coe_inv, commutatorElement_def, inv_inv]
      group
    rw [h2]
    exact hNc _ (δ u).2 _ h1
  let c : ↥V →* ↥V ⧸ N.subgroupOf V :=
    { toFun := fun v => ((δ v : ↥V) : ↥V ⧸ N.subgroupOf V)
      map_one' := by
        have h1 : δ 1 = 1 := Subtype.ext (by simp [δ])
        simp only [h1, QuotientGroup.mk_one]
      map_mul' := by
        intro u v
        have h1 : δ (u * v) = v⁻¹ * δ u * v * δ v :=
          Subtype.ext (by simp only [δ, coe_mul, coe_inv]; group)
        simp only [h1, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        rw [mul_assoc ((v : ↥V ⧸ N.subgroupOf V)⁻¹), hcen u v, ← mul_assoc, inv_mul_cancel,
          one_mul] }
  intro v hv
  have h1 := TwoQuot.eq_one_of_isPerfect' c (fun u u' => hcen u (δ u')) ⟨v, hv⟩
  have h2 : ((δ ⟨v, hv⟩ : ↥V) : ↥V ⧸ N.subgroupOf V) = 1 := h1
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h2
  exact h2

omit [Finite G] in
theorem oddCoreIn_subgroupOf_normal (V : Subgroup G) : ((oddCoreIn V).subgroupOf V).Normal := by
  rw [show (oddCoreIn V).subgroupOf V = pPrimeCore 2 V from
    comap_map_eq_self_of_injective V.subtype_injective _]
  infer_instance

omit [Finite G] in
theorem commutator_mem_oddCoreIn_of_isSolvable {K S : Subgroup G}
    (hq : IsQuasisimple (K ⧸ pPrimeCore 2 K)) (hSK : S ≤ K) (hn : (S.subgroupOf K).Normal)
    (hS : Group.IsSolvable S) {s u : G} (hs : s ∈ S) (hu : u ∈ K) : ⁅s, u⁆ ∈ oddCoreIn K := by
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥K) with hπ
  have hn' : ((S.subgroupOf K).map π).Normal := hn.map π (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hn' with htop | hcen
  · exfalso
    have : Group.IsSolvable ↥(S.subgroupOf K) :=
      Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe hSK).toMonoidHom)
        (subgroupOfEquivOfLe hSK).injective
    have : Group.IsSolvable ↥((S.subgroupOf K).map π) :=
      Group.isSolvable_of_surjective (π.subgroupMap_surjective _)
    let e := (MulEquiv.subgroupCongr htop).trans
      (Subgroup.topEquiv (G := ↥K ⧸ pPrimeCore 2 ↥K))
    have : Group.IsSolvable (↥K ⧸ pPrimeCore 2 ↥K) :=
      Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    obtain ⟨hperf, -, a, b, hab⟩ := hq
    have : Nontrivial (↥K ⧸ pPrimeCore 2 ↥K) := by
      by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      apply hab
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      rw [Subsingleton.elim a' b']
    exact Group.IsPerfect.not_isSolvable (↥K ⧸ pPrimeCore 2 ↥K) inferInstance
  · have h1 : π ⟨s, hSK hs⟩ ∈ center (↥K ⧸ pPrimeCore 2 ↥K) :=
      hcen (mem_map_of_mem π (show (⟨s, hSK hs⟩ : ↥K) ∈ S.subgroupOf K from hs))
    have h2 : π ⁅(⟨s, hSK hs⟩ : ↥K), ⟨u, hu⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_center_iff.mp h1 _).symm
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact mem_map.mpr ⟨_, h2, by simp [commutatorElement_def]⟩

theorem le_coreActionKernel_of_isSolvable {C K₁ K₂ R : Subgroup G} (h1 : K₁ ≤ C) (h2 : K₂ ≤ C)
    (hc1 : IsPComponent 2 (K₁.subgroupOf C)) (hc2 : IsPComponent 2 (K₂.subgroupOf C))
    (hRC : R ≤ C) (hRn : (R.subgroupOf C).Normal) (hR : Group.IsSolvable R)
    (hRV : R ≤ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G)) :
    R ≤ coreActionKernel (K₁ ⊔ K₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hn1, hn2, hO1, hO2⟩ := pComponent_sup_facts h1 h2 hc1 hc2
  have : Group.IsPerfect K₁ := isPerfect_of_isPComponent_subgroupOf h1 hc1
  have : Group.IsPerfect K₂ := isPerfect_of_isPComponent_subgroupOf h2 hc2
  have : Group.IsPerfect ↥(K₁ ⊔ K₂) := isPerfect_sup
  have hq1 := ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K₁ C h1).mp hc1).2.2
  have hq2 := ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K₂ C h2).mp hc2).2.2
  have hVC : K₁ ⊔ K₂ ≤ C := sup_le h1 h2
  have hRc : ∀ c ∈ C, ∀ r ∈ R, c * r * c⁻¹ ∈ R := by
    intro c hc r hr
    have h3 := hRn.conj_mem ⟨r, hRC hr⟩ hr ⟨c, hc⟩
    rw [mem_subgroupOf] at h3
    simpa only [coe_mul, coe_inv] using h3
  have hstep : ∀ {K : Subgroup G}, K ≤ C → Group.IsPerfect K →
      IsQuasisimple (K ⧸ pPrimeCore 2 K) → K₁ ⊔ K₂ ≤ normalizer (K : Set G) →
      ∀ s ∈ (K₁ ⊔ K₂) ⊓ R, s ∈ coreActionKernel K := by
    intro K hKC _ hq hVK s hs
    obtain ⟨hsV, hsR⟩ := mem_inf.mp hs
    have hsN : s ∈ normalizer (K : Set G) := hVK hsV
    have hKR : K ⊓ R ≤ K := inf_le_left
    have hKRn : ((K ⊓ R).subgroupOf K).Normal := by
      refine ⟨fun x hx k => ?_⟩
      rw [mem_subgroupOf] at hx ⊢
      obtain ⟨hxK, hxR⟩ := mem_inf.mp hx
      refine mem_inf.mpr ⟨mul_mem (mul_mem k.2 hxK) (inv_mem k.2), ?_⟩
      exact hRc _ (hKC k.2) _ hxR
    have hKRs : Group.IsSolvable ↥(K ⊓ R) :=
      Group.isSolvable_of_isSolvable_injective (inclusion_injective (inf_le_right : K ⊓ R ≤ R))
    refine mem_coreActionKernel.mpr ⟨hsN, ?_⟩
    refine commutator_mem_of_isPerfect' (map_subtype_le _) (oddCoreIn_subgroupOf_normal K) hsN
      fun k hk u hu => ?_
    have hδ : k⁻¹ * s⁻¹ * k * s ∈ K ⊓ R := by
      refine mem_inf.mpr ⟨?_, ?_⟩
      · have h3 := (mem_normalizer_iff.mp (inv_mem hsN) k).mp hk
        rw [inv_inv] at h3
        rw [show k⁻¹ * s⁻¹ * k * s = k⁻¹ * (s⁻¹ * k * s) by group]
        exact mul_mem (inv_mem hk) h3
      · have h3 := hRc k⁻¹ (inv_mem (hKC hk)) s⁻¹ (inv_mem hsR)
        rw [inv_inv] at h3
        exact mul_mem h3 hsR
    exact commutator_mem_oddCoreIn_of_isSolvable hq hKR hKRn hKRs hδ hu
  have hVR : ∀ s ∈ (K₁ ⊔ K₂) ⊓ R, s ∈ coreActionKernel (K₁ ⊔ K₂) := fun s hs =>
    mem_coreActionKernel_sup hO1 hO2 (hstep h1 inferInstance hq1 hn1 s hs)
      (hstep h2 inferInstance hq2 hn2 s hs)
  intro r hr
  have hrN := hRV hr
  refine mem_coreActionKernel.mpr ⟨hrN, ?_⟩
  refine commutator_mem_of_isPerfect' (map_subtype_le _) (oddCoreIn_subgroupOf_normal _) hrN
    fun v hv u hu => ?_
  set δ := v⁻¹ * r⁻¹ * v * r with hδ
  have hδVR : δ ∈ (K₁ ⊔ K₂) ⊓ R := by
    refine mem_inf.mpr ⟨?_, ?_⟩
    · have h3 := (mem_normalizer_iff.mp (inv_mem hrN) v).mp hv
      rw [inv_inv] at h3
      rw [hδ, show v⁻¹ * r⁻¹ * v * r = v⁻¹ * (r⁻¹ * v * r) by group]
      exact mul_mem (inv_mem hv) h3
    · have h3 := hRc v⁻¹ (inv_mem (hVC hv)) r⁻¹ (inv_mem hr)
      rw [inv_inv] at h3
      exact mul_mem h3 hr
  have hδK := (mem_coreActionKernel.mp (hVR δ hδVR)).2 u⁻¹ (inv_mem hu)
  have hδV : δ ∈ K₁ ⊔ K₂ := (mem_inf.mp hδVR).1
  have h4 : ⁅δ, u⁆ = δ * (u⁻¹⁻¹ * δ⁻¹ * u⁻¹ * δ) * δ⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [h4]
  have h5 := conj_mem_oddCoreIn hδK (inv_mem hδV)
  rwa [inv_inv] at h5

end Solvable

section Standard

variable {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']

omit [Finite G'] in
theorem mem_centralizer_of_map {f : G →* G'} {L : Subgroup G} [Group.IsPerfect L]
    (hodd : Odd (Nat.card f.ker)) (hkc : f.ker ≤ centralizer (L : Set G)) {g : G}
    (hg : f g ∈ centralizer ((L.map f : Subgroup G') : Set G')) : g ∈ centralizer (L : Set G) := by
  have : Group.IsSolvable f.ker := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hLc : L ≤ centralizer (f.ker : Set G) := le_centralizer_iff.mp hkc
  have hLg : conjugate L g = L := by
    have hcg : conjugate L g ≤ centralizer (f.ker : Set G) := by
      intro z hz
      rw [mem_conjugate_iff] at hz
      rw [mem_centralizer_iff]
      intro k hk
      have hk' : g * k * g⁻¹ ∈ f.ker :=
        (inferInstance : f.ker.Normal).conj_mem k hk g
      have h1 := mem_centralizer_iff.mp (hLc hz) _ hk'
      calc k * z = g⁻¹ * ((g * k * g⁻¹) * (g * z * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * z * g⁻¹) * (g * k * g⁻¹)) * g := by rw [h1]
        _ = z * k := by group
    have : Group.IsPerfect (conjugate L g) := Group.IsPerfect.map _
    refine TwoQuot.eq_of_map_eq_of_le_centralizer f hcg hLc ?_
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [SetLike.mem_coe, mem_conjugate_iff] at hz
      have h1 := mem_centralizer_iff.mp hg (f (g * z * g⁻¹)) (mem_map_of_mem f hz)
      refine ⟨g * z * g⁻¹, hz, ?_⟩
      rw [map_mul, map_mul, map_inv] at h1 ⊢
      have h2 : f g * f z = f g * (f g * f z * (f g)⁻¹) := by rw [← h1]; group
      exact (mul_left_cancel h2).symm
    · rintro ⟨z, hz, rfl⟩
      refine ⟨g⁻¹ * z * g, ?_, ?_⟩
      · rw [SetLike.mem_coe, mem_conjugate_iff, show g * (g⁻¹ * z * g) * g⁻¹ = z by group]
        exact hz
      · have h1 := mem_centralizer_iff.mp hg (f z) (mem_map_of_mem f hz)
        rw [map_mul, map_mul, map_inv]
        calc (f g)⁻¹ * f z * f g = (f g)⁻¹ * (f z * f g) := by group
          _ = (f g)⁻¹ * (f g * f z) := by rw [h1]
          _ = f z := by group
  have hgN : g ∈ normalizer (L : Set G) := mem_normalizer_of_conjugate_eq hLg
  have h1 := TwoQuot.commutator_mem_of_isPerfect (N := ⊥) bot_le
    (by rw [bot_subgroupOf]; infer_instance) (inv_mem hgN) fun l hl => by
      refine ⟨1, one_mem _, l⁻¹ * g⁻¹⁻¹ * l * g⁻¹, ?_, by rw [one_mul]⟩
      have hk : l⁻¹ * g⁻¹⁻¹ * l * g⁻¹ ∈ f.ker := by
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv, inv_inv]
        have h2 := mem_centralizer_iff.mp hg (f l) (mem_map_of_mem f hl)
        rw [show (f l)⁻¹ * f g * f l * (f g)⁻¹ = (f l)⁻¹ * (f g * f l) * (f g)⁻¹ by group,
          ← h2]
        group
      exact hkc hk
  rw [mem_centralizer_iff]
  intro l hl
  have h2 := h1 l hl
  rw [mem_bot, inv_inv] at h2
  calc l * g = l * (l⁻¹ * g * l * g⁻¹) * g := by rw [h2, mul_one]
    _ = g * l := by group

omit [Finite G'] in
theorem centralizer_map_eq_of_odd {f : G →* G'} (hf : Function.Surjective f) {L : Subgroup G}
    [Group.IsPerfect L] (hodd : Odd (Nat.card f.ker)) (hkc : f.ker ≤ centralizer (L : Set G)) :
    centralizer ((L.map f : Subgroup G') : Set G') = (centralizer (L : Set G)).map f := by
  apply le_antisymm
  · intro g' hg'
    obtain ⟨g, rfl⟩ := hf g'
    exact mem_map_of_mem f (mem_centralizer_of_map hodd hkc hg')
  · rintro _ ⟨g, hg, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hg l hl]

omit [Finite G] [Finite G'] in
theorem mem_map_iff_of_ker_le {f : G →* G'} {Y : Subgroup G} (hkY : f.ker ≤ Y) {x : G} :
    f x ∈ Y.map f ↔ x ∈ Y := by
  constructor
  · rintro ⟨z, hz, hzx⟩
    have h1 : z⁻¹ * x ∈ f.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hzx, inv_mul_cancel]
    rw [show x = z * (z⁻¹ * x) by group]
    exact mul_mem hz (hkY h1)
  · exact mem_map_of_mem f

omit [Finite G] [Finite G'] in
theorem mem_normalizer_map_iff {f : G →* G'} (hf : Function.Surjective f) {Y : Subgroup G}
    (hkY : f.ker ≤ Y) {g : G} :
    f g ∈ normalizer ((Y.map f : Subgroup G') : Set G') ↔ g ∈ normalizer (Y : Set G) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h1 z
    have h2 := h1 (f z)
    rwa [← map_inv, ← map_mul, ← map_mul, mem_map_iff_of_ker_le hkY,
      mem_map_iff_of_ker_le hkY] at h2
  · intro h1 z'
    obtain ⟨z, rfl⟩ := hf z'
    rw [← map_inv, ← map_mul, ← map_mul, mem_map_iff_of_ker_le hkY, mem_map_iff_of_ker_le hkY]
    exact h1 z

omit [Finite G] [Finite G'] in
theorem mem_normalizer_of_map {f : G →* G'} {L : Subgroup G} [Group.IsPerfect L]
    [Group.IsSolvable f.ker] (hkc : f.ker ≤ centralizer (L : Set G)) {g : G}
    (hg : f g ∈ normalizer ((L.map f : Subgroup G') : Set G')) : g ∈ normalizer (L : Set G) := by
  have hLc : L ≤ centralizer (f.ker : Set G) := le_centralizer_iff.mp hkc
  have hcg : conjugate L g ≤ centralizer (f.ker : Set G) := by
    intro z hz
    rw [mem_conjugate_iff] at hz
    rw [mem_centralizer_iff]
    intro k hk
    have hk' : g * k * g⁻¹ ∈ f.ker := (inferInstance : f.ker.Normal).conj_mem k hk g
    have h1 := mem_centralizer_iff.mp (hLc hz) _ hk'
    calc k * z = g⁻¹ * ((g * k * g⁻¹) * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * (g * k * g⁻¹)) * g := by rw [h1]
      _ = z * k := by group
  have : Group.IsPerfect (conjugate L g) := Group.IsPerfect.map _
  apply mem_normalizer_of_conjugate_eq
  refine TwoQuot.eq_of_map_eq_of_le_centralizer f hcg hLc ?_
  have h2 := conjugate_eq_of_mem_normalizer hg
  rw [← h2]
  exact map_conjugate _ _ _

omit [Finite G] in
theorem isStandardSubgroup_subgroupOf {L H : Subgroup G} (hLH : L ≤ H)
    (hstd : IsStandardSubgroup L)
    (heven : Even (Nat.card (centralizer ((L.subgroupOf H : Subgroup H) : Set H)))) :
    IsStandardSubgroup (L.subgroupOf H) :=
  CFSG.IsStandardSubgroup.subgroupOf hstd hLH heven

omit [Finite G] [Finite G'] in
theorem card_map_mul_card_ker {f : G →* G'} {Y : Subgroup G} (hkY : f.ker ≤ Y) :
    Nat.card (Y.map f) * Nat.card f.ker = Nat.card Y := by
  set φ := f.subgroupMap Y with hφ
  have hker : Nat.card φ.ker = Nat.card f.ker := by
    have h1 : φ.ker = f.ker.subgroupOf Y := by
      ext z
      rw [MonoidHom.mem_ker, mem_subgroupOf, MonoidHom.mem_ker]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [h1]
    exact Nat.card_congr (subgroupOfEquivOfLe hkY).toEquiv
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ
    (f.subgroupMap_surjective Y)).toEquiv, hker] at h2
  exact h2.symm

omit [Finite G] [Finite G'] in
theorem map_inf_of_ker_le {f : G →* G'} {A D : Subgroup G} (hkA : f.ker ≤ A) :
    (A ⊓ D).map f = A.map f ⊓ D.map f := by
  apply le_antisymm
  · exact le_inf (map_mono inf_le_left) (map_mono inf_le_right)
  · rintro _ ⟨hA, ⟨d, hd, rfl⟩⟩
    have hdA := (mem_map_iff_of_ker_le hkA).mp hA
    exact mem_map_of_mem f (mem_inf.mpr ⟨hdA, hd⟩)

omit [Finite G] [Finite G'] in
theorem map_mem_normalizer {f : G →* G'} {Y : Subgroup G} {g : G}
    (hg : g ∈ normalizer (Y : Set G)) : f g ∈ normalizer ((Y.map f : Subgroup G') : Set G') := by
  apply mem_normalizer_of_conjugate_eq
  rw [← map_conjugate, conjugate_eq_of_mem_normalizer hg]

omit [Finite G'] in
theorem isStandardSubgroup_map {f : G →* G'} (hf : Function.Surjective f) {L : Subgroup G}
    (hstd : IsStandardSubgroup L) (hodd : Odd (Nat.card f.ker))
    (hkc : f.ker ≤ centralizer (L : Set G)) : IsStandardSubgroup (L.map f) :=
  CFSG.ComponentClassification.GSThmB.isStandardSubgroup_map_of_surjective f hf hstd hodd hkc

omit [Finite G] in
theorem isComponent_subgroupOf_centralizer {L H : Subgroup G} {t : G} (htH : t ∈ H)
    (hLH : L ≤ H) (hLt : L ≤ centralizer ({t} : Set G))
    (hc : IsComponent (L.subgroupOf (centralizer ({t} : Set G)))) :
    L.subgroupOf H ≤ centralizer ({(⟨t, htH⟩ : H)} : Set H) ∧
      IsComponent ((L.subgroupOf H).subgroupOf (centralizer ({(⟨t, htH⟩ : H)} : Set H))) := by
  set C := centralizer ({t} : Set G) with hCdef
  have hCt : centralizer ({(⟨t, htH⟩ : H)} : Set H) = C.subgroupOf H := by
    ext z
    rw [mem_centralizer_singleton_iff, mem_subgroupOf, mem_centralizer_singleton_iff]
    exact ⟨fun h1 => congrArg Subtype.val h1, fun h1 => Subtype.ext h1⟩
  rw [hCt]
  refine ⟨fun z hz => hLt hz, ?_⟩
  obtain ⟨hq, hs⟩ := hc
  have hs' : (L.subgroupOf (C ⊓ H)).IsSubnormal := hs.comap (inclusion inf_le_left)
  have hLCH : L ≤ C ⊓ H := le_inf hLt hLH
  have hq' : IsQuasisimple ↥(L.subgroupOf (C ⊓ H)) :=
    (LocalAnalysis.ComponentInitial.isQuasisimple_congr
      ((subgroupOfEquivOfLe hLt).trans (subgroupOfEquivOfLe hLCH).symm)).1 hq
  let e : ↥(C ⊓ H) ≃* ↥(C.subgroupOf H) :=
    { toFun := fun x => ⟨⟨x, x.2.2⟩, x.2.1⟩
      invFun := fun x => ⟨x.1, x.2, x.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have h1 := LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent e ⟨hq', hs'⟩
  have he : (L.subgroupOf (C ⊓ H)).map e.toMonoidHom =
      (L.subgroupOf H).subgroupOf (C.subgroupOf H) := by
    ext ⟨⟨z, hzH⟩, hzC⟩
    rw [mem_map, mem_subgroupOf, mem_subgroupOf]
    constructor
    · rintro ⟨w, hw, hwz⟩
      show z ∈ L
      have h2 : (w : G) = z := congrArg (fun x : ↥(C.subgroupOf H) => ((x : H) : G)) hwz
      rw [← h2]
      exact hw
    · intro hz
      exact ⟨⟨z, hzC, hzH⟩, hz, rfl⟩
  rwa [he] at h1

omit [Finite G] [Finite G'] in
theorem isComponent_map_centralizer {f : G →* G'} (hf : Function.Surjective f)
    (hodd : Odd (Nat.card f.ker)) {L : Subgroup G} (hkc : f.ker ≤ centralizer (L : Set G))
    {t : G} (ht : t * t = 1) (hLt : L ≤ centralizer ({t} : Set G))
    (hc : IsComponent (L.subgroupOf (centralizer ({t} : Set G)))) :
    L.map f ≤ centralizer ({f t} : Set G') ∧
      IsComponent ((L.map f).subgroupOf (centralizer ({f t} : Set G'))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCt : centralizer ({f t} : Set G') = (centralizer ({t} : Set G)).map f := by
    have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht]
    have hE : IsPGroup 2 (zpowers t) := by
      rintro ⟨g, hg⟩
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
      refine ⟨1, Subtype.ext ?_⟩
      show (t ^ k) ^ 2 ^ 1 = 1
      rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, Nat.cast_ofNat, ht2,
        one_zpow]
    have hker : ¬ 2 ∣ Nat.card (f.domRestrict (⊤ : Subgroup G)).ker := by
      rw [MonoidHom.ker_domRestrict, Nat.card_congr (subgroupOfEquivOfLe le_top).toEquiv]
      exact Nat.odd_iff.mp hodd |> fun h => by omega
    have h1 := OddQuot.map_inf_centralizer f hE (by rw [normalizer_eq_top]; exact le_top) hker
    rw [top_inf_eq, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hf, top_inf_eq,
      MonoidHom.map_zpowers, centralizer_zpowers_eq, centralizer_zpowers_eq] at h1
    exact h1.symm
  rw [hCt]
  refine ⟨map_mono hLt, ?_⟩
  set φ := f.subgroupMap (centralizer ({t} : Set G)) with hφ
  rw [← OddQuot.map_subgroupOf_subgroupMap f hLt]
  obtain ⟨hq, hs⟩ := hc
  refine ⟨CFSG.LocalCores.isQuasisimple_of_surjective hq (φ.subgroupMap _)
    (φ.subgroupMap_surjective _) fun k hk => ?_, hs.map (f.subgroupMap_surjective _)⟩
  rw [mem_center_iff]
  intro m
  have hk' : (((k : ↥(L.subgroupOf (centralizer ({t} : Set G)))) : ↥(centralizer ({t} : Set G))) :
      G) ∈ f.ker := by
    rw [MonoidHom.mem_ker] at hk ⊢
    have h1 : φ (k : ↥(centralizer ({t} : Set G))) = 1 := congrArg Subtype.val hk
    exact congrArg Subtype.val h1
  exact Subtype.ext (Subtype.ext (mem_centralizer_iff.mp (hkc hk') _ m.2))

omit [Finite G'] in
theorem isSolvable_oddTwoCore (A : Type*) [Group A] [Finite A] :
    Group.IsSolvable ↥(oddTwoCore A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pPrimeCore 2 A ≤ oddTwoCore A := by
    intro x hx
    show QuotientGroup.mk' (pPrimeCore 2 A) x ∈ pCore 2 (A ⧸ pPrimeCore 2 A)
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have : Group.IsSolvable ↥(pPrimeCore 2 A) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  have : Group.IsNilpotent ↥(pCore 2 (A ⧸ pPrimeCore 2 A)) := CFSG.pCore_isPGroup.isNilpotent
  let g : ↥(oddTwoCore A) →* ↥(pCore 2 (A ⧸ pPrimeCore 2 A)) :=
    ((QuotientGroup.mk' (pPrimeCore 2 A)).comp (oddTwoCore A).subtype).codRestrict _
      fun x => x.2
  refine Group.isSolvable_of_ker_le_range (inclusion hO) g fun x hx => ?_
  rw [MonoidHom.mem_ker] at hx
  have h1 : QuotientGroup.mk' (pPrimeCore 2 A) (x : A) = 1 := congrArg Subtype.val hx
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨⟨x, h1⟩, rfl⟩

end Standard

end B5a

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

abbrev secW0 (h : Hyp52 X) (y : X) : Subgroup X := h.W ⊓ h.secG0 y

@[expose] noncomputable def secSigma (h : Hyp52 X) (y : X) : ↥(h.secW0 y) →* Wbar h.B :=
  (wbarMk h.B).comp (inclusion inf_le_left)

@[expose] noncomputable def secPhi (h : Hyp52 X) (y : X) :
    ↥(h.secW0 y) →* ↥(normalizer (h.secImage y h.B : Set (h.secBar y))) :=
  ((h.secMk y).comp (inclusion inf_le_right)).codRestrict _
    fun w => secMk_mem_normalizer w.2.2 w.2.1

@[expose] noncomputable def secRho (h : Hyp52 X) (y : X) :
    ↥(h.secW0 y) →* Wbar (h.secImage y h.B) :=
  (wbarMk (h.secImage y h.B)).comp (h.secPhi y)

theorem secPhi_coe (w : ↥(h.secW0 y)) :
    ((h.secPhi y w : ↥(normalizer (h.secImage y h.B : Set (h.secBar y)))) : h.secBar y) =
      h.secMk y ⟨w, w.2.2⟩ := rfl

theorem secPhi_surjective (hc : h.SecCond y) : Function.Surjective (h.secPhi y) := by
  rintro ⟨z, hz⟩
  have hz' := hz
  rw [hc.normalizer_secB] at hz'
  obtain ⟨g, hg, rfl⟩ := mem_map.mp hz'
  exact ⟨⟨g, hg, g.2⟩, rfl⟩

theorem secRho_surjective (hc : h.SecCond y) : Function.Surjective (h.secRho y) :=
  (QuotientGroup.mk'_surjective _).comp (secPhi_surjective hc)

theorem ker_secSigma_le (hc : h.SecCond y) : (h.secSigma y).ker ≤ (h.secRho y).ker := by
  intro w hw
  rw [MonoidHom.mem_ker] at hw ⊢
  have h1 : inclusion (inf_le_left : h.secW0 y ≤ h.W) w ∈ oddTwoCore ↥h.W := by
    rw [← QuotientGroup.eq_one_iff]
    exact hw
  have h2 := B5a.mem_oddTwoCore_of_injective _ (inclusion_injective _) h1
  have h3 := B5a.map_mem_oddTwoCore (h.secPhi y) (secPhi_surjective hc) h2
  show QuotientGroup.mk' _ (h.secPhi y w) = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact h3

theorem oddTwoCore_secW_le (hc : h.SecCond y) :
    (oddTwoCore ↥(normalizer (h.secImage y h.B : Set (h.secBar y)))).map
      (normalizer (h.secImage y h.B : Set (h.secBar y))).subtype ≤
      coreActionKernel (h.secImage y h.V) := by
  set Wp := normalizer (h.secImage y h.B : Set (h.secBar y)) with hWp
  obtain ⟨hK1, hK1c⟩ := isPComponent_secK hc (Or.inl rfl)
  obtain ⟨hK2, hK2c⟩ := isPComponent_secK hc (Or.inr rfl)
  rw [secImage_conjugate h.K hc.a_mem_G0] at hK2 hK2c
  have hV := secImage_V hc
  have hRn : (((oddTwoCore ↥Wp).map Wp.subtype).subgroupOf Wp).Normal := by
    rw [show ((oddTwoCore ↥Wp).map Wp.subtype).subgroupOf Wp = oddTwoCore ↥Wp from
      comap_map_eq_self_of_injective Wp.subtype_injective _]
    infer_instance
  have : Group.IsSolvable ↥(oddTwoCore ↥Wp) := B5a.isSolvable_oddTwoCore ↥Wp
  have hRs : Group.IsSolvable ↥((oddTwoCore ↥Wp).map Wp.subtype) :=
    Group.isSolvable_of_surjective (Wp.subtype.subgroupMap_surjective _)
  have hRV : (oddTwoCore ↥Wp).map Wp.subtype ≤ normalizer
      ((h.secImage y h.K ⊔ conjugate (h.secImage y h.K) hc.secA : Subgroup (h.secBar y)) :
        Set (h.secBar y)) := by
    rw [← hV, ← layerIn_secW hc]
    exact (map_subtype_le _).trans (OddQuot.le_normalizer_layerIn _)
  rw [hV]
  exact B5a.le_coreActionKernel_of_isSolvable hK1 hK2 hK1c hK2c (map_subtype_le _) hRn hRs hRV

theorem mem_coreActionKernel_of_mem_ker_secRho (hc : h.SecCond y) {w : ↥(h.secW0 y)}
    (hw : w ∈ (h.secRho y).ker) : (w : X) ∈ coreActionKernel h.V := by
  rw [MonoidHom.mem_ker] at hw
  have h1 : h.secPhi y w ∈ oddTwoCore ↥(normalizer (h.secImage y h.B : Set (h.secBar y))) := by
    rw [← QuotientGroup.eq_one_iff]
    exact hw
  have h2 : h.secMk y ⟨w, w.2.2⟩ ∈ coreActionKernel (h.secImage y h.V) :=
    oddTwoCore_secW_le hc (mem_map_of_mem _ h1)
  have : Group.IsPerfect h.V := isPerfect_V
  exact mem_coreActionKernel_of_secMk (h.V_le_G0 y) (h.V_le_centralizer_secB0 y) w.2.2
    (OddQuot.le_normalizer_layerIn _ w.2.1) h2

theorem B_le_ker_secSigma_secRho :
    h.B.subgroupOf (h.secW0 y) ≤ (h.secSigma y).ker ⊓ (h.secRho y).ker := by
  have hB2 := B5a.isPGroup_B h
  intro b hb
  have hb' : (b : X) ∈ h.B := hb
  refine mem_inf.mpr ⟨?_, ?_⟩
  · rw [MonoidHom.mem_ker]
    show QuotientGroup.mk' _ (inclusion (inf_le_left : h.secW0 y ≤ h.W) b) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine B5a.le_oddTwoCore (M := h.B.subgroupOf h.W) normal_in_normalizer (fun m hm => ?_) hb
    obtain ⟨k, hk⟩ := hB2 ⟨m, hm⟩
    refine ⟨k, ?_⟩
    have hk' : m ^ 2 ^ k = 1 := by
      apply Subtype.ext
      have h5 := congrArg Subtype.val hk
      simpa using h5
    rw [hk']
    exact one_mem _
  · rw [MonoidHom.mem_ker]
    show QuotientGroup.mk' _ (h.secPhi y b) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hBbar : IsPGroup 2 (h.secImage y h.B) :=
      (hB2.comap_subtype (K := h.secG0 y)).map (h.secMk y)
    refine B5a.le_oddTwoCore (M := (h.secImage y h.B).subgroupOf
      (normalizer (h.secImage y h.B : Set (h.secBar y)))) normal_in_normalizer
      (fun m hm => ?_) (show h.secPhi y b ∈ _ from mem_map_of_mem _ hb)
    obtain ⟨k, hk⟩ := hBbar ⟨m, hm⟩
    refine ⟨k, ?_⟩
    have hk' : m ^ 2 ^ k = 1 := by
      have h5 : ((m : h.secBar y)) ^ 2 ^ k = 1 := by
        have h6 := congrArg Subtype.val hk
        simpa using h6
      exact Subtype.ext (by rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact h5)
    rw [hk']
    exact one_mem _

theorem odd_card_map_ker_secRho (hc : h.SecCond y) :
    Odd (Nat.card ((h.secRho y).ker.map (h.secSigma y).rangeRestrict)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Kρ := (h.secRho y).ker with hKρ
  set σr := (h.secSigma y).rangeRestrict with hσr
  have hle : σr.ker ≤ Kρ := by
    rw [MonoidHom.ker_rangeRestrict]
    exact ker_secSigma_le hc
  have h1 := B5a.card_map_mul_card_ker hle
  set B' := h.B.subgroupOf (h.secW0 y) with hB'
  have hBW : h.B ≤ h.secW0 y := le_inf le_normalizer hc.B_le_G0
  have hcB : Nat.card B' = Nat.card h.B := Nat.card_congr (subgroupOfEquivOfLe hBW).toEquiv
  have hBσ : B' ≤ σr.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact (B_le_ker_secSigma_secRho).trans inf_le_left
  obtain ⟨j, hj⟩ := Subgroup.card_dvd_of_le hBσ
  set Kρ' := Kρ.map (h.secW0 y).subtype with hKρ'
  have hBK : h.B ≤ Kρ' := by
    intro b hb
    exact ⟨⟨b, hBW hb⟩, ((B_le_ker_secSigma_secRho).trans inf_le_right) hb, rfl⟩
  have hKC : Kρ' ≤ h.W ⊓ coreActionKernel h.V := by
    rintro _ ⟨w, hw, rfl⟩
    exact mem_inf.mpr ⟨w.2.1, mem_coreActionKernel_of_mem_ker_secRho hc hw⟩
  obtain ⟨R, hR⟩ := h.B_sylow_kernel
  have hodd : ¬ 2 ∣ h.B.relIndex (h.W ⊓ coreActionKernel h.V) := by
    rw [relIndex, ← hR]
    exact R.not_dvd_index
  have hrel := Subgroup.relIndex_mul_relIndex h.B Kρ' _ hBK hKC
  have hodd' : ¬ 2 ∣ h.B.relIndex Kρ' := fun h2 => hodd (hrel ▸ dvd_mul_of_dvd_left h2 _)
  have h2 := Subgroup.relIndex_mul_card (H := h.B) (K := Kρ')
  rw [inf_of_le_left hBK] at h2
  have hcK : Nat.card Kρ' = Nat.card Kρ :=
    (Nat.card_congr (Kρ.equivMapOfInjective _ (h.secW0 y).subtype_injective).toEquiv).symm
  have hBpos : 0 < Nat.card h.B := Nat.card_pos
  have h3 : Nat.card (Kρ.map σr) * j = h.B.relIndex Kρ' := by
    apply Nat.eq_of_mul_eq_mul_right hBpos
    calc Nat.card (Kρ.map σr) * j * Nat.card h.B = Nat.card (Kρ.map σr) * Nat.card σr.ker := by
          rw [hj, hcB]; ring
      _ = Nat.card Kρ := h1
      _ = h.B.relIndex Kρ' * Nat.card h.B := by rw [h2, hcK]
  have h4 : ¬ 2 ∣ Nat.card (Kρ.map σr) := fun h5 => hodd' (h3 ▸ dvd_mul_of_dvd_left h5 _)
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h4)

omit [Finite X] in
theorem pPrimeCore_le_oddTwoCore (A : Type*) [Group A] : pPrimeCore 2 A ≤ oddTwoCore A := by
  intro x hx
  show QuotientGroup.mk' (pPrimeCore 2 A) x ∈ pCore 2 (A ⧸ pPrimeCore 2 A)
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
  exact one_mem _

@[expose] noncomputable def secTau (hc : h.SecCond y) :
    ↥(h.secSigma y).range →* Wbar (h.secImage y h.B) :=
  (QuotientGroup.lift (h.secSigma y).rangeRestrict.ker (h.secRho y)
    (by rw [MonoidHom.ker_rangeRestrict]; exact ker_secSigma_le hc)).comp
    (QuotientGroup.quotientKerEquivOfSurjective _
      (h.secSigma y).rangeRestrict_surjective).symm.toMonoidHom

theorem secTau_apply (hc : h.SecCond y) (w : ↥(h.secW0 y)) :
    secTau hc ((h.secSigma y).rangeRestrict w) = h.secRho y w := by
  have he : (QuotientGroup.quotientKerEquivOfSurjective (h.secSigma y).rangeRestrict
      (h.secSigma y).rangeRestrict_surjective).symm ((h.secSigma y).rangeRestrict w) =
      (QuotientGroup.mk w : ↥(h.secW0 y) ⧸ (h.secSigma y).rangeRestrict.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [secTau, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, he, QuotientGroup.lift_mk]

theorem secTau_surjective (hc : h.SecCond y) : Function.Surjective (secTau hc) := by
  intro z
  obtain ⟨w, rfl⟩ := secRho_surjective hc z
  exact ⟨_, secTau_apply hc w⟩

theorem ker_secTau (hc : h.SecCond y) :
    (secTau hc).ker = (h.secRho y).ker.map (h.secSigma y).rangeRestrict := by
  have hle : (h.secSigma y).rangeRestrict.ker ≤ (h.secRho y).ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact ker_secSigma_le hc
  ext r
  obtain ⟨w, rfl⟩ := (h.secSigma y).rangeRestrict_surjective r
  rw [MonoidHom.mem_ker, secTau_apply, B5a.mem_map_iff_of_ker_le hle, MonoidHom.mem_ker]

theorem odd_card_ker_secTau (hc : h.SecCond y) : Odd (Nat.card (secTau hc).ker) := by
  rw [ker_secTau hc]
  exact odd_card_map_ker_secRho hc

theorem wbarImage_JB_le_range :
    wbarImage h.B (GSLit.fixedLayer h.J h.B) ≤ (h.secSigma y).range := by
  rintro _ ⟨j, hj, rfl⟩
  have hjV : (j : X) ∈ h.V := B5a.fixedLayer_le_V h hj
  exact ⟨⟨j, j.2, h.V_le_G0 y hjV⟩, rfl⟩

theorem ker_secTau_le_centralizer (hc : h.SecCond y) : (secTau hc).ker ≤
    centralizer (((wbarImage h.B (GSLit.fixedLayer h.J h.B)).subgroupOf (h.secSigma y).range :
      Subgroup ↥(h.secSigma y).range) : Set ↥(h.secSigma y).range) := by
  rw [ker_secTau hc]
  rintro _ ⟨w, hw, rfl⟩
  have hwK := mem_coreActionKernel_of_mem_ker_secRho hc hw
  have hOVW : oddCoreIn h.V ≤ oddCoreIn h.W :=
    B5a.oddCoreIn_le_of_le_normalizer V_le_W (OddQuot.le_normalizer_layerIn _)
  rw [mem_centralizer_iff]
  intro l hl
  obtain ⟨j, hj, hjl⟩ := mem_map.mp
    (show (l : Wbar h.B) ∈ wbarImage h.B (GSLit.fixedLayer h.J h.B) from hl)
  have hjV : (j : X) ∈ h.V := B5a.fixedLayer_le_V h hj
  set w' : ↥h.W := inclusion (inf_le_left : h.secW0 y ≤ h.W) w with hw'
  have h1 : ((j : X))⁻¹ * (w : X)⁻¹ * j * w ∈ oddCoreIn h.W :=
    hOVW ((mem_coreActionKernel.mp hwK).2 j hjV)
  obtain ⟨o, ho, hoe⟩ := mem_map.mp h1
  have h2 : o = j⁻¹ * w'⁻¹ * j * w' :=
    Subtype.ext (by simp only [coe_mul, coe_inv, hw', coe_inclusion]; exact hoe)
  have h3 : wbarMk h.B (j⁻¹ * w'⁻¹ * j * w') = 1 := by
    rw [← h2, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact pPrimeCore_le_oddTwoCore _ ho
  apply Subtype.ext
  show (l : Wbar h.B) * h.secSigma y w = h.secSigma y w * l
  rw [← hjl]
  show wbarMk h.B j * wbarMk h.B w' = wbarMk h.B w' * wbarMk h.B j
  simp only [map_mul, map_inv] at h3
  calc wbarMk h.B j * wbarMk h.B w' = wbarMk h.B w' * wbarMk h.B j *
        ((wbarMk h.B j)⁻¹ * (wbarMk h.B w')⁻¹ * wbarMk h.B j * wbarMk h.B w') := by group
    _ = wbarMk h.B w' * wbarMk h.B j := by rw [h3, mul_one]

theorem secSigma_a_ne_one (hc : h.SecCond y) :
    h.secSigma y ⟨h.a, h.a_mem_normalizer, hc.a_mem_G0⟩ ≠ 1 := by
  intro h1
  have ha : (⟨h.a, h.a_mem_normalizer⟩ : ↥h.W) ∈ oddTwoCore ↥h.W := by
    rw [← QuotientGroup.eq_one_iff]
    exact h1
  set M := (oddTwoCore ↥h.W).map h.W.subtype with hM
  have hVM : h.V ≤ M := by
    have h2 : ⁅h.V, zpowers h.a⁆ ≤ M := by
      rw [Subgroup.commutator_le]
      intro v hv z hz
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
      have hvW : v ∈ h.W := V_le_W hv
      have hk : (⟨h.a, h.a_mem_normalizer⟩ : ↥h.W) ^ k ∈ oddTwoCore ↥h.W := zpow_mem ha k
      have h3 : (⟨v, hvW⟩ : ↥h.W) * (⟨h.a, h.a_mem_normalizer⟩ ^ k) * (⟨v, hvW⟩ : ↥h.W)⁻¹ *
          (⟨h.a, h.a_mem_normalizer⟩ ^ k)⁻¹ ∈ oddTwoCore ↥h.W :=
        mul_mem ((inferInstance : (oddTwoCore ↥h.W).Normal).conj_mem _ hk _) (inv_mem hk)
      refine ⟨_, h3, ?_⟩
      simp [commutatorElement_def]
    rwa [h.commutator_eq] at h2
  have : Group.IsSolvable ↥(oddTwoCore ↥h.W) := B5a.isSolvable_oddTwoCore _
  have : Group.IsSolvable ↥M :=
    Group.isSolvable_of_surjective (h.W.subtype.subgroupMap_surjective _)
  have hVs : Group.IsSolvable ↥h.V :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hVM)
  have : Group.IsPerfect h.V := isPerfect_V
  have hV1 : h.V = ⊥ := by
    by_contra hne
    have : Nontrivial h.V := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable h.V hVs
  exact B5a.fixedLayer_ne_bot h (le_bot_iff.mp (hV1 ▸ B5a.fixedLayer_le_V h))

theorem even_card_centralizer_range (hc : h.SecCond y) :
    Even (Nat.card (centralizer (((wbarImage h.B (GSLit.fixedLayer h.J h.B)).subgroupOf
      (h.secSigma y).range : Subgroup ↥(h.secSigma y).range) : Set ↥(h.secSigma y).range))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t : ↥(h.secSigma y).range := (h.secSigma y).rangeRestrict
    ⟨h.a, h.a_mem_normalizer, hc.a_mem_G0⟩ with ht
  have htC : t ∈ centralizer (((wbarImage h.B (GSLit.fixedLayer h.J h.B)).subgroupOf
      (h.secSigma y).range : Subgroup ↥(h.secSigma y).range) : Set ↥(h.secSigma y).range) := by
    rw [mem_centralizer_iff]
    intro l hl
    obtain ⟨j, hj, hjl⟩ := mem_map.mp
      (show (l : Wbar h.B) ∈ wbarImage h.B (GSLit.fixedLayer h.J h.B) from hl)
    apply Subtype.ext
    show (l : Wbar h.B) * h.secSigma y ⟨h.a, h.a_mem_normalizer, hc.a_mem_G0⟩ =
      h.secSigma y ⟨h.a, h.a_mem_normalizer, hc.a_mem_G0⟩ * l
    rw [← hjl]
    show wbarMk h.B j * wbarMk h.B ⟨h.a, h.a_mem_normalizer⟩ =
      wbarMk h.B ⟨h.a, h.a_mem_normalizer⟩ * wbarMk h.B j
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp
      (h.J_le (((GSLit.fixedLayer_le_inf h.J h.B).trans inf_le_left) hj))
  have ht2 : orderOf t = 2 := by
    apply orderOf_eq_prime
    · rw [ht, ← map_pow]
      have h1 : (⟨h.a, h.a_mem_normalizer, hc.a_mem_G0⟩ : ↥(h.secW0 y)) ^ 2 = 1 := by
        apply Subtype.ext
        rw [coe_pow, ← h.orderOf_a, pow_orderOf_eq_one]
        rfl
      rw [h1, map_one]
    · intro h1
      apply secSigma_a_ne_one hc
      have h2 := congrArg Subtype.val h1
      exact h2
  rw [even_iff_two_dvd, ← ht2]
  have h3 := orderOf_dvd_natCard (⟨t, htC⟩ : centralizer (((wbarImage h.B
    (GSLit.fixedLayer h.J h.B)).subgroupOf (h.secSigma y).range : Subgroup ↥(h.secSigma y).range) :
      Set ↥(h.secSigma y).range))
  rwa [Subgroup.orderOf_mk] at h3

theorem map_secTau_eq (hc : h.SecCond y) :
    ((wbarImage h.B (GSLit.fixedLayer h.J h.B)).subgroupOf (h.secSigma y).range).map
      (secTau hc) = wbarImage (h.secImage y h.B) (h.secImage y (GSLit.fixedLayer h.J h.B)) := by
  ext z
  constructor
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨j, hj, hjl⟩ := mem_map.mp
      (show (l : Wbar h.B) ∈ wbarImage h.B (GSLit.fixedLayer h.J h.B) from hl)
    have hjV : (j : X) ∈ h.V := B5a.fixedLayer_le_V h hj
    have hjW0 : (j : X) ∈ h.secW0 y := ⟨j.2, h.V_le_G0 y hjV⟩
    have hl' : l = (h.secSigma y).rangeRestrict ⟨j, hjW0⟩ := Subtype.ext (by rw [← hjl]; rfl)
    rw [hl', secTau_apply]
    exact mem_map_of_mem _ (show h.secPhi y ⟨j, hjW0⟩ ∈
      (h.secImage y (GSLit.fixedLayer h.J h.B)).subgroupOf
        (normalizer (h.secImage y h.B : Set (h.secBar y))) from
      mem_map_of_mem _ (show (⟨j, h.V_le_G0 y hjV⟩ : ↥(h.secG0 y)) ∈
        (GSLit.fixedLayer h.J h.B).subgroupOf (h.secG0 y) from hj))
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨j, hj, hjp⟩ := mem_map.mp hp
    have hjV : (j : X) ∈ h.V := B5a.fixedLayer_le_V h hj
    have hjW0 : (j : X) ∈ h.secW0 y := ⟨V_le_W hjV, j.2⟩
    refine ⟨(h.secSigma y).rangeRestrict ⟨j, hjW0⟩, ?_, ?_⟩
    · exact mem_map_of_mem (wbarMk h.B) (show (⟨j, V_le_W hjV⟩ : ↥h.W) ∈
        (GSLit.fixedLayer h.J h.B).subgroupOf h.W from hj)
    · rw [secTau_apply]
      show wbarMk (h.secImage y h.B) (h.secPhi y ⟨j, hjW0⟩) = wbarMk (h.secImage y h.B) p
      congr 1
      apply Subtype.ext
      rw [secPhi_coe]
      exact hjp

theorem secTau_a (hc : h.SecCond y) :
    secTau hc ((h.secSigma y).rangeRestrict ⟨h.a, h.a_mem_normalizer, hc.a_mem_G0⟩) =
      wbarMk (h.secImage y h.B) ⟨hc.secA, hc.secA_mem_normalizer⟩ := by
  rw [secTau_apply]
  rfl

theorem isStandard_secBar (hc : h.SecCond y) :
    IsStandardSubgroup (wbarImage (h.secImage y h.B)
      (GSLit.fixedLayer (h.secImage y (h.secJ0 y)) (h.secImage y h.B))) := by
  rw [secFixedLayer_B hc]
  have h1 := B5a.isStandardSubgroup_subgroupOf wbarImage_JB_le_range h.isStandard_bar
    (even_card_centralizer_range hc)
  have h2 := B5a.isStandardSubgroup_map (secTau_surjective hc) h1 (odd_card_ker_secTau hc)
    (ker_secTau_le_centralizer hc)
  rwa [map_secTau_eq hc] at h2

theorem isComponent_secBar (hc : h.SecCond y) :
    wbarImage (h.secImage y h.B) (GSLit.fixedLayer (h.secImage y (h.secJ0 y))
      (h.secImage y h.B)) ≤ centralizer ({(wbarMk (h.secImage y h.B)
        ⟨hc.secA, hc.secA_mem_normalizer⟩)} : Set (Wbar (h.secImage y h.B))) ∧
    IsComponent ((wbarImage (h.secImage y h.B) (GSLit.fixedLayer (h.secImage y (h.secJ0 y))
      (h.secImage y h.B))).subgroupOf (centralizer ({(wbarMk (h.secImage y h.B)
        ⟨hc.secA, hc.secA_mem_normalizer⟩)} : Set (Wbar (h.secImage y h.B))))) := by
  rw [secFixedLayer_B hc]
  obtain ⟨hLC, hcomp⟩ := h.isComponent_bar
  have htH : wbarMk h.B ⟨h.a, h.a_mem_normalizer⟩ ∈ (h.secSigma y).range :=
    ⟨⟨h.a, h.a_mem_normalizer, hc.a_mem_G0⟩, rfl⟩
  obtain ⟨h1, h2⟩ := B5a.isComponent_subgroupOf_centralizer htH wbarImage_JB_le_range hLC hcomp
  have hteq : (⟨wbarMk h.B ⟨h.a, h.a_mem_normalizer⟩, htH⟩ : ↥(h.secSigma y).range) =
      (h.secSigma y).rangeRestrict ⟨h.a, h.a_mem_normalizer, hc.a_mem_G0⟩ := rfl
  have ht : (⟨wbarMk h.B ⟨h.a, h.a_mem_normalizer⟩, htH⟩ : ↥(h.secSigma y).range) *
      ⟨wbarMk h.B ⟨h.a, h.a_mem_normalizer⟩, htH⟩ = 1 := by
    apply Subtype.ext
    show wbarMk h.B ⟨h.a, h.a_mem_normalizer⟩ * wbarMk h.B ⟨h.a, h.a_mem_normalizer⟩ = 1
    rw [← map_mul]
    have h3 : (⟨h.a, h.a_mem_normalizer⟩ : ↥h.W) * ⟨h.a, h.a_mem_normalizer⟩ = 1 := by
      apply Subtype.ext
      show h.a * h.a = 1
      rw [← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]
    rw [h3, map_one]
  obtain ⟨h4, h5⟩ := B5a.isComponent_map_centralizer (secTau_surjective hc)
    (odd_card_ker_secTau hc) (ker_secTau_le_centralizer hc) ht h1 h2
  rw [hteq, secTau_a hc, map_secTau_eq hc] at h4 h5
  exact ⟨h4, h5⟩

end Hyp52

end CFSG.ComponentClassification.GSThmB
