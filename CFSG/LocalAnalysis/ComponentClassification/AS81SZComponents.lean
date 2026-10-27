module

public import CFSG.LocalAnalysis.ComponentClassification.AS81QbarMain
import CFSG.Goldschmidt.Steps.IHConseq
import CFSG.Goldschmidt.Steps.Ind

public section

namespace CFSG.ComponentClassification.AS81.SZ

open Subgroup CFSG.Open CFSG.Goldschmidt CFSG.LocalCores CFSG.ABGLocalTools
open CFSG.ComponentClassification.AS81.Qbar

theorem exists_derivedSeries_le_ker_of_card_le_six {H ι : Type*} [Group H] [Finite ι]
    (hι : Nat.card ι ≤ 6)
    (hperm : ∀ φ : H →* Equiv.Perm (Fin 6), ∃ n : ℕ, derivedSeries H n ≤ φ.ker)
    (π : H →* Equiv.Perm ι) : ∃ n : ℕ, derivedSeries H n ≤ π.ker := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨e⟩ : Nonempty (ι ↪ Fin 6) := Function.Embedding.nonempty_of_card_le (by
    rw [← Nat.card_eq_fintype_card, Fintype.card_fin]
    exact hι)
  obtain ⟨n, hn⟩ := hperm ((Equiv.Perm.viaEmbeddingHom e).comp π)
  refine ⟨n, fun h hh => ?_⟩
  have h1 := hn hh
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at h1
  rw [MonoidHom.mem_ker]
  exact Equiv.Perm.viaEmbeddingHom_injective e (by rw [h1, map_one])

theorem exists_derivedSeries_sameOn_components_of_perm {Y : Type} [Group Y] [Finite Y]
    (S : Sylow 2 Y) {A : Subgroup Y}
    (htype : ∀ K : ComponentIndex Y, goldschmidtSimpleType (K.1 ⧸ center K.1))
    (hind : ∀ K : ComponentIndex Y, InducesOmega1 A K.1 S) {H : Type*} [Group H]
    (σ : H →* MulAut Y) (hσA : ∀ h, ∀ a ∈ A, σ h a ∈ A)
    (hperm : ∃ m₀ : ℕ, derivedSeries H m₀ ≤ (compPermHom.comp σ).ker) :
    ∃ m : ℕ, ∀ h ∈ derivedSeries H m, ∀ a ∈ A, ∀ K : ComponentIndex Y, ∀ x ∈ K.1,
      (σ h a)⁻¹ * x * σ h a = a⁻¹ * x * a := by
  obtain ⟨m₀, h0⟩ := hperm
  set π : H →* Equiv.Perm (ComponentIndex Y) := compPermHom.comp σ with hπ
  have hfix : ∀ h ∈ π.ker, ∀ K : ComponentIndex Y, ∀ x ∈ K.1, σ h x ∈ K.1 := by
    intro h hh K x hx
    rw [MonoidHom.mem_ker] at hh
    have hK : compPerm (σ h) K = K := congrArg (fun e : Equiv.Perm (ComponentIndex Y) => e K) hh
    exact apply_mem_of_compPerm hK hx
  have hK : ∀ K : ComponentIndex Y, ∃ m : ℕ, ∀ h ∈ derivedSeries π.ker m, ∀ a ∈ A, ∀ x ∈ K.1,
      (σ h a)⁻¹ * x * σ h a = a⁻¹ * x * a := fun K =>
    exists_derivedSeries_sameOn S K.2 (htype K) (hind K) (σ.comp π.ker.subtype)
      (fun h a ha => hσA h a ha) (fun h x hx => hfix h h.2 K x hx)
  choose mK hmK using hK
  refine ⟨m₀ + Finset.univ.sup mK, fun h hh a ha K x hx => ?_⟩
  obtain ⟨h', hh', rfl⟩ := derivedSeries_add_le h0 (Finset.univ.sup mK) hh
  have hle : derivedSeries π.ker (Finset.univ.sup mK) ≤ derivedSeries π.ker (mK K) :=
    derivedSeries_antitone π.ker (Finset.le_sup (f := mK) (Finset.mem_univ K))
  exact hmK K h' (hle hh') a ha x hx

section Central

variable {H : Type} [Group H]

@[expose] def closureMod (N₀ : Subgroup H) [N₀.Normal] (Q : Subgroup H) :
    Subgroup (H ⧸ N₀) :=
  normalClosure ((Q.map (QuotientGroup.mk' N₀) : Subgroup (H ⧸ N₀)) : Set (H ⧸ N₀))

@[expose] def NoComponentMod (N₀ : Subgroup H) [N₀.Normal] (Q : Subgroup H) : Prop :=
  goldschmidtLayer (↥(closureMod N₀ Q) ⧸ goldschmidtOddCore ↥(closureMod N₀ Q)) = ⊥

end Central

section FourGroup

variable {G : Type} [Group G]

instance subgroupOf_centralizer_normal (Z : Subgroup G) :
    (Z.subgroupOf (centralizer (Z : Set G))).Normal :=
  ⟨fun n hn h => by
    rw [mem_subgroupOf] at hn ⊢
    have e : (h : G) * n = n * h := (mem_centralizer_iff.mp h.2 n hn).symm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e, mul_inv_cancel_right]
    exact hn⟩

theorem le_centralizer_of_elemAbelian {Z : Subgroup G} (hZ : IsElemAbelian 2 Z) :
    Z ≤ centralizer (Z : Set G) := fun z hz => mem_centralizer_iff.mpr fun w hw =>
  congrArg Subtype.val (hZ.1.is_comm.comm ⟨w, hw⟩ ⟨z, hz⟩)

variable [Finite G]

theorem noComponentMod_of_action
    {Z S T N : Subgroup G} (hZ : IsElemAbelian 2 Z)
    (hZ4 : Nat.card Z = 4) (hT : IsSylowOf 2 T (centralizer (Z : Set G))) (hST : S ≤ T)
    (hZS : Z ≤ S) (hS14 : Nat.card S = 2 ^ 14)
    (hSab : ∀ x ∈ S, ∀ y ∈ S, x * y * x⁻¹ * y⁻¹ ∈ Z)
    (hcl : ∀ x ∈ S, ∀ h ∈ centralizer (Z : Set G), h⁻¹ * x * h ∈ T → h⁻¹ * x * h ∈ S)
    (hNC : N ≤ centralizer (Z : Set G)) (hNS : N ≤ normalizer (S : Set G))
    (hN : ∀ B : Subgroup G, Z ≤ B → B < S → N ≤ normalizer (B : Set G) → ∀ n : ℕ,
      ∃ k ∈ (derivedSeries N n).map N.subtype, ∃ x ∈ S, k⁻¹ * x * k * x⁻¹ ∉ B)
    (hperm : ∀ φ : ↥N →* Equiv.Perm (Fin 6), ∃ n : ℕ, derivedSeries ↥N n ≤ φ.ker) :
    NoComponentMod (Z.subgroupOf (centralizer (Z : Set G)))
      (S.subgroupOf (centralizer (Z : Set G))) := by
  have hZC := le_centralizer_of_elemAbelian hZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold NoComponentMod closureMod
  set C := centralizer (Z : Set G) with hCdef
  obtain ⟨T₀, hT₀⟩ := hT
  have hTC : T ≤ C := hT₀ ▸ map_subtype_le _
  have hSC : S ≤ C := hST.trans hTC
  set S' := S.subgroupOf C with hS'
  have hS'T : S' ≤ (T₀ : Subgroup C) := by
    intro x hx
    have hxS : (x : G) ∈ T := hST (mem_subgroupOf.mp hx)
    rw [← hT₀] at hxS
    obtain ⟨y, hy, hyx⟩ := hxS
    rwa [← Subtype.ext hyx]
  have hcl' : ∀ x ∈ S', ∀ h : C, h⁻¹ * x * h ∈ (T₀ : Subgroup C) → h⁻¹ * x * h ∈ S' :=
    fun x hx h hh => by
      rw [mem_subgroupOf]
      refine hcl _ (mem_subgroupOf.mp hx) _ h.2 ?_
      rw [← hT₀]
      exact ⟨_, hh, rfl⟩
  set Zc := Z.subgroupOf C with hZcdef
  have hSab' : ∀ x ∈ S', ∀ y ∈ S', x * y * x⁻¹ * y⁻¹ ∈ Zc := fun x hx y hy => by
    rw [mem_subgroupOf]
    exact hSab _ (mem_subgroupOf.mp hx) _ (mem_subgroupOf.mp hy)
  set π₀ := QuotientGroup.mk' Zc with hπ₀
  have hπ₀s : Function.Surjective π₀ := QuotientGroup.mk'_surjective Zc
  have hker : π₀.ker = Zc := QuotientGroup.ker_mk' Zc
  have hZcS' : Zc ≤ S' := fun x hx => mem_subgroupOf.mpr (hZS (mem_subgroupOf.mp hx))
  have hZcT : Zc ≤ (T₀ : Subgroup C) := hZcS'.trans hS'T
  set Sb : Sylow 2 (C ⧸ Zc) := T₀.mapSurjective hπ₀s with hSb
  have hSbcoe : (Sb : Subgroup (C ⧸ Zc)) = (T₀ : Subgroup C).map π₀ :=
    Sylow.coe_mapSurjective _ _
  set Qb := S'.map π₀ with hQb
  have hQbS : Qb ≤ Sb := by
    rw [hSbcoe]
    exact map_mono hS'T
  have hQbab : IsMulCommutative Qb := by
    refine isMulCommutative_iff_of_setLike.mpr ?_
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hπ₀, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have := hSab' _ (S'.inv_mem hb) _ (S'.inv_mem ha)
    simpa [mul_assoc] using this
  have hQbcl : fusionStronglyClosed (Qb : Set (C ⧸ Zc)) (Sb : Subgroup (C ⧸ Zc)) := by
    rintro _ ⟨a, ha, rfl⟩ g hg
    obtain ⟨h, rfl⟩ := hπ₀s g
    rw [← map_inv, ← map_mul, ← map_mul] at hg ⊢
    rw [hSbcoe] at hg
    obtain ⟨s, hs, hse⟩ := hg
    have hmem : h⁻¹ * a * h ∈ (T₀ : Subgroup C) := by
      have h1 : s⁻¹ * (h⁻¹ * a * h) ∈ Zc := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hse, inv_mul_cancel]
      have h2 := (T₀ : Subgroup C).mul_mem hs (hZcT h1)
      simpa [mul_assoc] using h2
    exact ⟨_, hcl' a ha h hmem, rfl⟩
  have hIH : IH (Nat.card (C ⧸ Zc) + 1) := fun Z _ _ _ => coreStatement_iff.mp coreStatement Z
  have hTsyl : fusionIsSylowIn 2 (Sb : Subgroup (C ⧸ Zc)) ⊤ :=
    ⟨le_top, Sb.isPGroup', fun P _ hP hTP => Sb.is_maximal' hP hTP⟩
  obtain ⟨hConc, -, -, hC3, -⟩ := N16_of N1 _ hIH (C ⧸ Zc) Sb Qb ⊤ Sb hQbS hQbab hQbcl hQbS hTsyl
    (by rw [card_top]; omega)
  set M : Subgroup (C ⧸ Zc) := normalClosureIn ⊤ Qb with hMdef
  have hMeq : M = normalClosure (Qb : Set (C ⧸ Zc)) := by
    rw [hMdef, normalClosureIn, map_normalClosure _ _ (fun y => ⟨⟨y, mem_top y⟩, rfl⟩)]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_subgroupOf.1 hx
    · intro hy
      exact ⟨⟨y, mem_top y⟩, mem_subgroupOf.2 hy, rfl⟩
  suffices hgoal : goldschmidtLayer (↥M ⧸ goldschmidtOddCore ↥M) = ⊥ by
    have e : ∀ M₁ M₂ : Subgroup (C ⧸ Zc), M₁ = M₂ →
        goldschmidtLayer (↥M₁ ⧸ goldschmidtOddCore ↥M₁) = ⊥ →
        goldschmidtLayer (↥M₂ ⧸ goldschmidtOddCore ↥M₂) = ⊥ := by
      rintro M₁ M₂ rfl h
      exact h
    exact e M _ hMeq hgoal
  have hMn : M.Normal := by
    rw [hMeq]
    exact normalClosure_normal
  have hQbM : Qb ≤ M := by
    rw [hMeq]
    exact le_normalClosure
  set π := QuotientGroup.mk' (goldschmidtOddCore M) with hπ
  obtain ⟨PM, hPM⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Sb hMn.isSubnormal
  have hPMeq : (PM : Subgroup M) = (Sb : Subgroup (C ⧸ Zc)).subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [hPM, subgroupOf_map_subtype]
  have hQbPM : Qb.subgroupOf M ≤ (PM : Subgroup M) := by
    rw [hPMeq]
    exact fun x hx => mem_subgroupOf.2 (hQbS (mem_subgroupOf.1 hx))
  have hclM := stronglyClosed_subgroupOf Sb hQbcl hQbM PM hQbPM
  obtain ⟨Sbar, hSbar, hclbar⟩ := CFSG.ShultStronglyClosedTI.quotient_stronglyClosed PM
    (Qb.subgroupOf M) (goldschmidtOddCore M) hQbPM hclM
  set A := (Qb.subgroupOf M).map π with hA
  have hASbar : A ≤ Sbar := by
    rw [hSbar]
    exact map_mono hQbPM
  have hAab : IsMulCommutative A := isMulCommutative_map (isMulCommutative_subgroupOf hQbab M) π
  have hO : goldschmidtOddCore (M ⧸ goldschmidtOddCore M) = ⊥ :=
    goldschmidtOddCore_quotient_eq_bot M
  have hSbarT : (Sbar : Subgroup (M ⧸ goldschmidtOddCore M)) = barOf M Sb := by
    rw [hSbar, hPMeq]
    rfl
  have hopen : ∀ K : ComponentIndex (M ⧸ goldschmidtOddCore M), IsComponentOf K.1 ⊤ :=
    fun K => (CFSG.isComponent_iff_open K.1).mp K.2
  have htype : ∀ K : ComponentIndex (M ⧸ goldschmidtOddCore M),
      goldschmidtSimpleType (K.1 ⧸ center K.1) := fun K => hConc.2.2 K.1 (hopen K)
  have hind : ∀ K : ComponentIndex (M ⧸ goldschmidtOddCore M), InducesOmega1 A K.1 Sbar :=
    fun K => by
      rw [hSbarT]
      exact hC3 K.1 (hopen K)
  have hcover : ∀ K : ComponentIndex (M ⧸ goldschmidtOddCore M), ∀ a ∈ A, ∃ x ∈ A ⊓ K.1,
      ∀ y ∈ K.1, a⁻¹ * y * a = x⁻¹ * y * x :=
    fun K => N17_of N11b _ Sbar A K.1 hASbar hAab hclbar hO (hopen K) (htype K) (hind K)
  have hcard : Nat.card A < 4 ^ 7 := by
    have h1 : Nat.card A ≤ Nat.card (Qb.subgroupOf M) := natCard_map_le π _
    have h2 : Nat.card (Qb.subgroupOf M) = Nat.card Qb :=
      Nat.card_congr (subgroupOfEquivOfLe hQbM).toEquiv
    have h3 : Nat.card Qb * 4 = 2 ^ 14 := by
      have e1 := relIndex_ker (K := S') π₀
      have e2 := relIndex_mul_card π₀.ker S'
      rw [hker, inf_of_le_left hZcS'] at e2
      rw [hker] at e1
      have e3 : Nat.card Zc = 4 := by
        rw [← hZ4]
        exact Nat.card_congr (subgroupOfEquivOfLe hZC).toEquiv
      have e4 : Nat.card S' = 2 ^ 14 := by
        rw [← hS14]
        exact Nat.card_congr (subgroupOfEquivOfLe hSC).toEquiv
      rw [e1, e3, e4] at e2
      exact e2
    omega
  have hιM : ∀ x : S, π₀ (inclusion hSC x) ∈ M := fun x =>
    hQbM (mem_map.mpr ⟨inclusion hSC x, mem_subgroupOf.mpr x.2, rfl⟩)
  set ι : S →* M ⧸ goldschmidtOddCore M :=
    π.comp ((π₀.comp (inclusion hSC)).codRestrict M hιM) with hι
  have hιA : ∀ x : S, ι x ∈ A := by
    intro x
    refine mem_map.mpr ⟨⟨π₀ (inclusion hSC x), hιM x⟩, ?_, rfl⟩
    rw [mem_subgroupOf]
    exact mem_map.mpr ⟨inclusion hSC x, mem_subgroupOf.mpr x.2, rfl⟩
  have hιsurj : ∀ a ∈ A, ∃ x : S, ι x = a := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : (w : C ⧸ Zc) ∈ Qb := hw
    obtain ⟨c, hc, hcw⟩ := mem_map.mp hw'
    refine ⟨⟨c, mem_subgroupOf.mp hc⟩, ?_⟩
    rw [hι, MonoidHom.comp_apply]
    exact congrArg π (Subtype.ext hcw)
  set σ : N →* MulAut (M ⧸ goldschmidtOddCore M) :=
    (MonoidHom.mk' (Asc76X.conjQuot hMn) (Asc76X.conjQuot_mul hMn)).comp
      (π₀.comp (inclusion hNC)) with hσ
  have hNS' : ∀ (n : N) (x : S), (n : G) * x * (n : G)⁻¹ ∈ S := fun n x =>
    (mem_normalizer_iff.mp (hNS n.2) x).mp x.2
  have hequiv : ∀ (n : N) (x : S), σ n (ι x) = ι ⟨(n : G) * x * (n : G)⁻¹, hNS' n x⟩ :=
    fun n x => rfl
  have hσA : ∀ n, ∀ a ∈ A, σ n a ∈ A := by
    intro n a ha
    obtain ⟨x, rfl⟩ := hιsurj a ha
    rw [hequiv]
    exact hιA _
  have hc6 : Nat.card (ComponentIndex (M ⧸ goldschmidtOddCore M)) ≤ 6 := by
    have h1 := four_pow_card_componentIndex_le Sbar htype hind hcover
    by_contra hcon
    push Not at hcon
    have h2 : 4 ^ 7 ≤ 4 ^ Nat.card (ComponentIndex (M ⧸ goldschmidtOddCore M)) :=
      Nat.pow_le_pow_right (by norm_num) hcon
    omega
  have hpermc := exists_derivedSeries_le_ker_of_card_le_six hc6 hperm (compPermHom.comp σ)
  by_contra hne
  obtain ⟨K₀, hK₀⟩ : ∃ K : Subgroup (M ⧸ goldschmidtOddCore M), IsComponentOf K ⊤ := by
    by_contra hcon
    push Not at hcon
    apply hne
    rw [goldschmidtLayer, sSup_eq_bot]
    intro K hK
    exact absurd hK (hcon K)
  have hK₀' : IsComponent K₀ := (CFSG.isComponent_iff_open K₀).mpr hK₀
  set B : Subgroup G :=
    ((compCentralizer (M ⧸ goldschmidtOddCore M)).comap ι).map S.subtype with hB
  have hmemB : ∀ x : S, (x : G) ∈ B ↔ ι x ∈ compCentralizer (M ⧸ goldschmidtOddCore M) := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = x := Subtype.ext hyx
      subst hyx'
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hBS : B ≤ S := map_subtype_le _
  have hZB : Z ≤ B := by
    intro z hz
    have h1 : (π₀.comp (inclusion hSC)).codRestrict M hιM ⟨z, hZS hz⟩ = 1 := by
      apply Subtype.ext
      change π₀ (inclusion hSC ⟨z, hZS hz⟩) = 1
      rw [hπ₀, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact mem_subgroupOf.mpr hz
    have h2 : ι ⟨z, hZS hz⟩ = 1 := by
      rw [hι, MonoidHom.comp_apply, h1, map_one]
    exact (hmemB ⟨z, hZS hz⟩).mpr (by rw [h2]; exact one_mem _)
  have hBlt : B < S := by
    refine lt_of_le_of_ne hBS fun hBSeq => ?_
    obtain ⟨a, ha, y, hy, hay⟩ :=
      exists_mem_conj_ne Sbar hK₀' (htype ⟨K₀, hK₀'⟩) (hind ⟨K₀, hK₀'⟩)
    obtain ⟨x, rfl⟩ := hιsurj a ha
    have hxB : (x : G) ∈ B := by
      rw [hBSeq]
      exact x.2
    have h1 := (mem_compCentralizer.mp ((hmemB x).mp hxB)) ⟨K₀, hK₀'⟩ y hy
    apply hay
    rw [mul_assoc, h1, inv_mul_cancel_left]
  have hNB : N ≤ normalizer (B : Set G) := by
    intro n hn
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxS := hBS hx
      refine (hmemB ⟨_, hNS' ⟨n, hn⟩ ⟨x, hxS⟩⟩).mpr ?_
      rw [← hequiv ⟨n, hn⟩ ⟨x, hxS⟩]
      exact apply_mem_compCentralizer (σ ⟨n, hn⟩) ((hmemB ⟨x, hxS⟩).mp hx)
    · intro hx
      have hxS' := hBS hx
      have hxS : x ∈ S := (mem_normalizer_iff.mp (hNS hn) x).mpr hxS'
      refine (hmemB ⟨x, hxS⟩).mpr ?_
      have h1 := (hmemB ⟨_, hxS'⟩).mp hx
      rw [← hequiv ⟨n, hn⟩ ⟨x, hxS⟩] at h1
      have h2 := apply_mem_compCentralizer (σ ⟨n, hn⟩)⁻¹ h1
      rwa [MulAut.inv_apply_self] at h2
  obtain ⟨m, hm⟩ := exists_derivedSeries_sameOn_components_of_perm Sbar htype hind σ hσA hpermc
  obtain ⟨k, hk, x, hx, hkx⟩ := hN B hZB hBlt hNB m
  obtain ⟨k', hk', rfl⟩ := hk
  apply hkx
  have hwS : (N.subtype k')⁻¹ * x * N.subtype k' * x⁻¹ ∈ S :=
    S.mul_mem (by simpa using hNS' k'⁻¹ ⟨x, hx⟩) (S.inv_mem hx)
  have hιw : ι ⟨_, hwS⟩ = σ k'⁻¹ (ι ⟨x, hx⟩) * (ι ⟨x, hx⟩)⁻¹ := by
    have e1 : (⟨_, hwS⟩ : S) = ⟨_, hNS' k'⁻¹ ⟨x, hx⟩⟩ * (⟨x, hx⟩ : S)⁻¹ :=
      Subtype.ext (by simp)
    rw [e1, map_mul, map_inv, ← hequiv]
  refine (hmemB ⟨_, hwS⟩).mpr ?_
  rw [hιw, mem_compCentralizer]
  intro K y hy
  have h1 := hm k'⁻¹ (inv_mem hk') (ι ⟨x, hx⟩) (hιA _) K y hy
  calc y * (σ k'⁻¹ (ι ⟨x, hx⟩) * (ι ⟨x, hx⟩)⁻¹) =
      σ k'⁻¹ (ι ⟨x, hx⟩) * ((σ k'⁻¹ (ι ⟨x, hx⟩))⁻¹ * y * σ k'⁻¹ (ι ⟨x, hx⟩)) *
        (ι ⟨x, hx⟩)⁻¹ := by group
    _ = σ k'⁻¹ (ι ⟨x, hx⟩) * ((ι ⟨x, hx⟩)⁻¹ * y * ι ⟨x, hx⟩) * (ι ⟨x, hx⟩)⁻¹ := by rw [h1]
    _ = σ k'⁻¹ (ι ⟨x, hx⟩) * (ι ⟨x, hx⟩)⁻¹ * y := by group

end FourGroup

end CFSG.ComponentClassification.AS81.SZ
