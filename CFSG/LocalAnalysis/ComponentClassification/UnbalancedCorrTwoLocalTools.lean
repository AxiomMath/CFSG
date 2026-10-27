module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrOddTimesTwoTransport
public import CFSG.LocalAnalysis.ComponentClassification.UGSChainKGroupTwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UGSChainOrbitTools

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem isPComponent_subgroupOf_of_isSubnormal {L Y Z : Subgroup G} (hLY : L ≤ Y) (hYZ : Y ≤ Z)
    (hY : (Y.subgroupOf Z).IsSubnormal) (hL : IsPComponent 2 (L.subgroupOf Y)) :
    IsPComponent 2 (L.subgroupOf Z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← isPComponent_subgroupOf_subgroupOf_iff' hYZ 2 Nat.prime_two] at hL
  exact (CatalogueBPrimeJoin.pComponent_subnormal_overgroup_iff 2 (L.subgroupOf Z)
    (Y.subgroupOf Z) (fun _ hx => hLY hx) hY).mp hL

theorem isPComponent_subgroupOf_of_le {L Y Z : Subgroup G} (hLY : L ≤ Y) (hYZ : Y ≤ Z)
    (hL : IsPComponent 2 (L.subgroupOf Z)) : IsPComponent 2 (L.subgroupOf Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← isPComponent_subgroupOf_subgroupOf_iff' hYZ 2 Nat.prime_two]
  exact CatalogueBPrimeJoin.pComponent_restrict_overgroup 2 hL (fun _ hx => hLY hx)

omit [Finite G] in
theorem conjugate_le_of_mem {M H : Subgroup G} (hMH : M ≤ H) {g : G} (hg : g ∈ H) :
    conjugate M g ≤ H := fun x hx => by
  rw [UnbalancedLayer.mem_conjugate_iff] at hx
  have h := mul_mem (mul_mem (inv_mem hg) (hMH hx)) hg
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h

omit [Finite G] in
theorem isPComponent_conjugate_subgroupOf {M H : Subgroup G} {g : G} (hg : g ∈ H)
    (hM : IsPComponent 2 (M.subgroupOf H)) : IsPComponent 2 ((conjugate M g).subgroupOf H) := by
  have h := UnbalancedLayer.isPComponent_conjugate hM (⟨g, hg⟩ : H)
  rwa [UnbalancedLayer.conjugate_subgroupOf_eq] at h

omit [Finite G] in
theorem exists_quotient_equiv_of_sup {T J : Subgroup G} (hTJ : T ≤ J)
    (hsup : T ⊔ (pPrimeCore 2 J).map J.subtype = J)
    (hcore : (pPrimeCore 2 T).map T.subtype = T ⊓ (pPrimeCore 2 J).map J.subtype) :
    ∃ e : T ⧸ pPrimeCore 2 T ≃* J ⧸ pPrimeCore 2 J,
      ∀ (t : T) (j : J), (t : G) = j → e t = j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : T →* J ⧸ pPrimeCore 2 J := (QuotientGroup.mk' (pPrimeCore 2 J)).comp (inclusion hTJ)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hsup' : T.subgroupOf J ⊔ pPrimeCore 2 J = ⊤ := by
      apply map_injective J.subtype_injective
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hTJ, ← MonoidHom.range_eq_map, range_subtype,
        hsup]
    have hj : j ∈ ((T.subgroupOf J ⊔ pPrimeCore 2 J : Subgroup J) : Set J) := by
      rw [hsup']
      exact mem_top j
    rw [mul_normal] at hj
    obtain ⟨t, ht, o, ho, rfl⟩ := Set.mem_mul.mp hj
    refine ⟨⟨t, ht⟩, ?_⟩
    show (QuotientGroup.mk' (pPrimeCore 2 J)) t = (QuotientGroup.mk' (pPrimeCore 2 J)) (t * o)
    have h1 : (QuotientGroup.mk' (pPrimeCore 2 J)) o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
    rw [map_mul, h1, mul_one]
  have hker : pPrimeCore 2 T = f.ker := by
    ext x
    rw [MonoidHom.mem_ker]
    show _ ↔ (QuotientGroup.mk' (pPrimeCore 2 J)) (inclusion hTJ x) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have h1 : x ∈ pPrimeCore 2 T ↔ (x : G) ∈ T ⊓ (pPrimeCore 2 J).map J.subtype := by
      rw [← hcore]
      constructor
      · exact fun hx => mem_map_of_mem _ hx
      · intro hx
        obtain ⟨y, hy, hyx⟩ := mem_map.mp hx
        rwa [← Subtype.ext hyx]
    rw [h1]
    constructor
    · rintro ⟨-, hx⟩
      obtain ⟨y, hy, hyx⟩ := mem_map.mp hx
      rwa [show inclusion hTJ x = y from Subtype.ext hyx.symm]
    · intro hx
      exact ⟨x.2, mem_map_of_mem J.subtype hx⟩
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf), fun t j htj => ?_⟩
  have hj : inclusion hTJ t = j := Subtype.ext htj
  rw [← hj]
  rfl

theorem fixedLayer_facts {X J B T : Subgroup G} (hJX : J ≤ X)
    (hJsub : (J.subgroupOf X).IsSubnormal) (hBX : B ≤ X) (hBJ : B ≤ normalizer (J : Set G))
    (hB : IsPGroup 2 B) (hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J))
    (hcomm : ∀ b ∈ B, ∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype)
    (hT : T = (pLayer ↥(J ⊓ centralizer (B : Set G)) 2).map
      (J ⊓ centralizer (B : Set G)).subtype) :
    T ⊔ (pPrimeCore 2 J).map J.subtype = J ∧
      (pPrimeCore 2 T).map T.subtype = T ⊓ (pPrimeCore 2 J).map J.subtype ∧
      IsPComponent 2 (T.subgroupOf (X ⊓ centralizer (B : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J' := J.subgroupOf X with hJ'
  set B' := B.subgroupOf X with hB'
  have hcore : ∀ x : X, x ∈ (pPrimeCore 2 J').map J'.subtype ↔
      (x : G) ∈ (pPrimeCore 2 J).map J.subtype := by
    intro x
    have h3 := pPrimeCore_map_subgroupOf 2 J X hJX
    constructor
    · intro hx
      rw [← h3]
      exact mem_map_of_mem X.subtype hx
    · intro hx
      rw [← h3] at hx
      obtain ⟨y, hy, hyx⟩ := mem_map.mp hx
      have hyeq : y = x := Subtype.ext hyx
      rwa [← hyeq]
  have hBN : B' ≤ normalizer (J' : Set X) := fun b hb =>
    UnbalancedLayer.mem_normalizer_subgroupOf_of_mem (hBJ hb)
  have hB2 : IsPGroup 2 B' := hB.comap_of_injective X.subtype X.subtype_injective
  have hQ : IsQuasisimple (J' ⧸ pPrimeCore 2 J') :=
    LocalCores.isQuasisimple_of_mulEquiv
      (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 (subgroupOfEquivOfLe hJX)).symm
      hJq
  have hcomm' : ⁅J', B'⁆ ≤ (pPrimeCore 2 J').map J'.subtype := by
    rw [commutator_le]
    intro j hj b hb
    rw [hcore]
    have h1 := hcomm _ (inv_mem (show ((b : X) : G) ∈ B from hb)) _
      (inv_mem (show ((j : X) : G) ∈ J from hj))
    rw [inv_inv, inv_inv] at h1
    simpa [commutatorElement_def] using h1
  have hcen : centralizer ((B' : Subgroup X) : Set X) =
      (X ⊓ centralizer (B : Set G)).subgroupOf X := by
    ext x
    rw [mem_centralizer_iff, mem_subgroupOf, mem_inf, mem_centralizer_iff]
    constructor
    · intro h
      refine ⟨x.2, fun b hb => ?_⟩
      exact congrArg Subtype.val (h ⟨b, hBX hb⟩ hb)
    · intro h b hb
      exact Subtype.ext (h.2 b hb)
  have hC : J' ⊓ centralizer ((B' : Subgroup X) : Set X) =
      (J ⊓ centralizer (B : Set G)).subgroupOf X := by
    rw [hcen]
    ext x
    simp only [mem_inf, mem_subgroupOf, hJ']
    tauto
  obtain ⟨hsup, hcoreT, -, -, hpc, -⟩ :=
    UnbalancedGS.trivial_quotient_action_fixed_layer_is_p_component 2
      J' hJsub B' hBN hB2 hQ hcomm' _ rfl _ rfl
  have hTJ : T ≤ J := hT ▸ (map_subtype_le _).trans inf_le_left
  have hTX' : (pLayer ↥(J' ⊓ centralizer ((B' : Subgroup X) : Set X)) 2).map
      (J' ⊓ centralizer ((B' : Subgroup X) : Set X)).subtype = T.subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le (hTJ.trans hJX), hC, map_pLayer_subgroupOf_eq X _,
      inf_of_le_right (inf_le_left.trans hJX), hT]
  rw [hTX'] at hsup hcoreT hpc
  rw [hcen] at hpc
  refine ⟨?_, ?_, (isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2 Nat.prime_two).mp hpc⟩
  · have h := congrArg (map X.subtype) hsup
    rwa [Subgroup.map_sup, map_subgroupOf_eq_of_le (hTJ.trans hJX),
      pPrimeCore_map_subgroupOf 2 J X hJX, map_subgroupOf_eq_of_le hJX] at h
  · have h := congrArg (map X.subtype) hcoreT
    rwa [pPrimeCore_map_subgroupOf 2 T X (hTJ.trans hJX), map_inf_eq _ _ _ X.subtype_injective,
      map_subgroupOf_eq_of_le (hTJ.trans hJX), pPrimeCore_map_subgroupOf 2 J X hJX] at h

theorem pPrimeCore_normalizer_le_centralizer {B : Subgroup G} (hB : IsPGroup 2 B) :
    (pPrimeCore 2 ↥(normalizer (B : Set G))).map (normalizer (B : Set G)).subtype ≤
      centralizer (B : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (B : Set G) with hN
  have hB' : IsPGroup 2 (B.subgroupOf N) := hB.comap_of_injective N.subtype N.subtype_injective
  have hBn : (B.subgroupOf N).Normal := normal_in_normalizer
  have h1 : ⁅pPrimeCore 2 ↥N, B.subgroupOf N⁆ = ⊥ := by
    have h := commutator_le_inf (pPrimeCore 2 ↥N) (B.subgroupOf N)
    rw [inf_comm, inf_eq_bot_of_isPGroup_two hB' pPrimeCore_coprime_card] at h
    exact le_bot_iff.mp h
  intro r hr
  obtain ⟨r', hr', rfl⟩ := mem_map.mp hr
  rw [mem_centralizer_iff]
  intro b hb
  have h2 := commutator_mem_commutator hr'
    (show (⟨b, le_normalizer hb⟩ : N) ∈ B.subgroupOf N from hb)
  rw [h1, mem_bot] at h2
  exact (congrArg Subtype.val (commutatorElement_eq_one_iff_mul_comm.mp h2)).symm

omit [Finite G] in
theorem centralizer_le_normalizer' (B : Subgroup G) :
    centralizer (B : Set G) ≤ normalizer (B : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro h
  rw [mem_centralizer_iff] at hg
  constructor
  · intro hh
    rw [← hg h hh, mul_inv_cancel_right]
    exact hh
  · intro hh
    have h1 := hg _ hh
    have h2 : h = g * h * g⁻¹ := by
      calc h = g⁻¹ * ((g * h * g⁻¹) * g) := by group
        _ = g⁻¹ * (g * (g * h * g⁻¹)) := by rw [h1]
        _ = g * h * g⁻¹ := by group
    rw [h2]
    exact hh

omit [Finite G] in
theorem centralizer_normal_normalizer (B : Subgroup G) :
    ((centralizer (B : Set G)).subgroupOf (normalizer (B : Set G))).Normal := by
  refine ⟨fun c hc n => ?_⟩
  rw [mem_subgroupOf] at hc ⊢
  rw [mem_centralizer_iff] at hc ⊢
  intro b hb
  have hn : (n : G)⁻¹ * b * n ∈ B := by
    have := (mem_normalizer_iff.mp (inv_mem n.2) b).mp hb
    rwa [inv_inv] at this
  have h1 := hc _ hn
  simp only [coe_mul, coe_inv]
  calc b * ((n : G) * c * (n : G)⁻¹)
      = (n : G) * ((n : G)⁻¹ * b * n * c) * (n : G)⁻¹ := by group
    _ = (n : G) * (c * ((n : G)⁻¹ * b * n)) * (n : G)⁻¹ := by rw [h1]
    _ = (n : G) * c * (n : G)⁻¹ * b := by group

theorem pPrimeCore_normalizer_eq_centralizer {B : Subgroup G} (hB : IsPGroup 2 B) :
    (pPrimeCore 2 ↥(normalizer (B : Set G))).map (normalizer (B : Set G)).subtype =
      (pPrimeCore 2 ↥(centralizer (B : Set G))).map (centralizer (B : Set G)).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (B : Set G) with hN
  set C := centralizer (B : Set G) with hCdef
  have hCN : C ≤ N := centralizer_le_normalizer' B
  have hsub : (C.subgroupOf N).IsSubnormal := (centralizer_normal_normalizer B).isSubnormal
  have h := map_pPrimeCore_eq_inf_of_isSubnormal hsub
  have h' := congrArg (map N.subtype) h
  rw [pPrimeCore_map_subgroupOf 2 C N hCN, map_inf_eq _ _ _ N.subtype_injective,
    map_subgroupOf_eq_of_le hCN, inf_of_le_right (pPrimeCore_normalizer_le_centralizer hB)] at h'
  exact h'.symm

theorem exists_orbit_component {a : G} (ha : orderOf a = 2) {H T : Subgroup G} (haH : a ∈ H)
    (hT : T ≤ centralizer ({a} : Set G) ⊓ H)
    (hTpc : IsPComponent 2 (T.subgroupOf (centralizer ({a} : Set G) ⊓ H)))
    (hTE : T ≤ (pLayer ↥H 2).map H.subtype) :
    ∃ M : Subgroup G, M ≤ H ∧ IsPComponent 2 (M.subgroupOf H) ∧ T ≤ M ⊔ conjugate M a ∧
      IsPComponent 2 (T.subgroupOf ((M ⊔ conjugate M a) ⊓ centralizer ({a} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ca := centralizer ({a} : Set G) with hCa
  have hTH : T ≤ H := hT.trans inf_le_right
  have ha' : orderOf (⟨a, haH⟩ : H) = 2 := by rw [Subgroup.orderOf_mk]; exact ha
  have hcena := UGSChain.centralizer_mk_eq_subgroupOf haH
  have hT'C : T.subgroupOf H ≤ centralizer ({(⟨a, haH⟩ : H)} : Set H) := by
    rw [hcena]
    intro y hy
    exact mem_subgroupOf.mpr (hT (mem_subgroupOf.mp hy))
  have hT'pc : IsPComponent 2 ((T.subgroupOf H).subgroupOf
      (centralizer ({(⟨a, haH⟩ : H)} : Set H))) := by
    rw [hcena, isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2 Nat.prime_two]
    exact hTpc
  have hT'E : T.subgroupOf H ≤ pLayer H 2 := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := mem_map.mp (hTE (mem_subgroupOf.mp hy))
    rwa [← Subtype.ext hzy]
  obtain ⟨M', hM', hT'K, hT'Kpc⟩ :=
    UnbalancedLayer.two_layer_fixed_component_orbit_location ha' hT'C hT'pc hT'E
  obtain ⟨M, hMH, rfl⟩ : ∃ M : Subgroup G, M ≤ H ∧ M.subgroupOf H = M' :=
    ⟨M'.map H.subtype, map_subtype_le _, comap_map_eq_self_of_injective H.subtype_injective _⟩
  have hMaH : conjugate M a ≤ H := conjugate_le_of_mem hMH haH
  have hK'eq : M.subgroupOf H ⊔ conjugate (M.subgroupOf H) ⟨a, haH⟩ =
      (M ⊔ conjugate M a).subgroupOf H := by
    rw [UnbalancedLayer.conjugate_subgroupOf_eq M H ⟨a, haH⟩, subgroupOf_sup hMH hMaH]
  have hKH : M ⊔ conjugate M a ≤ H := sup_le hMH hMaH
  have hCeq : (M.subgroupOf H ⊔ conjugate (M.subgroupOf H) ⟨a, haH⟩) ⊓
      centralizer ({(⟨a, haH⟩ : H)} : Set H) = ((M ⊔ conjugate M a) ⊓ Ca).subgroupOf H := by
    rw [hK'eq, hcena]
    ext y
    simp only [mem_inf, mem_subgroupOf]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, y.2⟩⟩
  refine ⟨M, hMH, hM', fun t ht => ?_, ?_⟩
  · have h1 := hT'K (show (⟨t, hTH ht⟩ : H) ∈ T.subgroupOf H from ht)
    rw [hK'eq] at h1
    exact h1
  · rw [hCeq, isPComponent_subgroupOf_subgroupOf_iff' (inf_le_left.trans hKH) 2 Nat.prime_two]
      at hT'Kpc
    exact hT'Kpc

theorem iSup_conjugate_eq_orbit {H M T : Subgroup G} {a : G} (haH : a ∈ H)
    (hMH : M ≤ H) (hM : IsPComponent 2 (M.subgroupOf H))
    (hTK : T ≤ (M ⊔ conjugate M a) ⊓ centralizer ({a} : Set G))
    (hT : IsPComponent 2 (T.subgroupOf ((M ⊔ conjugate M a) ⊓ centralizer ({a} : Set G)))) :
    M ⊔ conjugate M a ≤ (pLayer ↥H 2).map H.subtype ∧
      (pLayer ↥H 2).map H.subtype ≤ normalizer ((M ⊔ conjugate M a : Subgroup G) : Set G) ∧
      (⨆ e ∈ (pLayer ↥H 2).map H.subtype, conjugate T e) = M ⊔ conjugate M a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := (pLayer ↥H 2).map H.subtype with hEdef
  set K := M ⊔ conjugate M a with hKdef
  have hMaH : conjugate M a ≤ H := conjugate_le_of_mem hMH haH
  have hMa : IsPComponent 2 ((conjugate M a).subgroupOf H) :=
    isPComponent_conjugate_subgroupOf haH hM
  have hKH : K ≤ H := sup_le hMH hMaH
  have hM₁E : M.subgroupOf H ≤ pLayer ↥H 2 := le_sSup hM
  have hMa₁E : (conjugate M a).subgroupOf H ≤ pLayer ↥H 2 := le_sSup hMa
  have hME : M ≤ E := fun y hy =>
    ⟨⟨y, hMH hy⟩, hM₁E (show (⟨y, hMH hy⟩ : H) ∈ M.subgroupOf H from hy), rfl⟩
  have hMaE : conjugate M a ≤ E := fun y hy =>
    ⟨⟨y, hMaH hy⟩, hMa₁E (show (⟨y, hMaH hy⟩ : H) ∈ (conjugate M a).subgroupOf H from hy),
      rfl⟩
  have hKE : K ≤ E := sup_le hME hMaE
  have hEM : E ≤ normalizer (M : Set G) := UGSChain.map_pLayer_le_normalizer hMH hM
  have hEMa : E ≤ normalizer (conjugate M a : Set G) := UGSChain.map_pLayer_le_normalizer hMaH hMa
  have hEK : E ≤ normalizer (K : Set G) := fun g hg => mem_normalizer_sup (hEM hg) (hEMa hg)
  refine ⟨hKE, hEK, ?_⟩
  set S := ⨆ e ∈ E, conjugate T e with hSdef
  have hTKk : T ≤ K := hTK.trans inf_le_left
  have hTC : T ≤ centralizer ({a} : Set G) := hTK.trans inf_le_right
  have hTH : T ≤ H := hTKk.trans hKH
  have hTS : T ≤ S := by
    have h1 : conjugate T 1 ≤ S := le_iSup₂_of_le (1 : G) (one_mem E) le_rfl
    rwa [UnbalancedLayer.conjugate_one] at h1
  have hSK : S ≤ K := iSup₂_le fun e he => by
    rw [← UnbalancedLayer.conjugate_eq_of_mem_normalizer (hEK he)]
    exact map_mono hTKk
  have hES : E ≤ normalizer (S : Set G) := fun g hg => mem_normalizer_iSup_conjugate_of_mem hg
  have haE : a ∈ normalizer (E : Set G) := by
    have : (pLayer ↥H 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
    exact UnbalancedGS.normalizer_le_normalizer_map_of_characteristic H (pLayer ↥H 2)
      (le_normalizer haH)
  have haT : a ∈ normalizer (T : Set G) :=
    UnbalancedLayer.mem_normalizer_of_conjugate_eq (conjugate_eq_self_of_le_centralizer hTC)
  have haS : a ∈ normalizer (S : Set G) := mem_normalizer_iSup_conjugate_of_normalizer haE haT
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥H) with hπ
  have hS₁M : S.subgroupOf H ≤ normalizer (M.subgroupOf H : Set H) := fun s hs =>
    UnbalancedLayer.mem_normalizer_subgroupOf_of_mem (hEM (hKE (hSK hs)))
  have hM₁S : M.subgroupOf H ≤ normalizer (S.subgroupOf H : Set H) := fun m hm =>
    UnbalancedLayer.mem_normalizer_subgroupOf_of_mem (hES (hME hm))
  obtain ⟨Kc, hKc, -, hmapM, -⟩ := id hM
  have hAq : IsQuasisimple ↥((M.subgroupOf H).map π) := by rw [hmapM]; exact hKc.1
  have hTperf : ⁅T, T⁆ = T := by
    have h1 : Group.IsPerfect ↥(T.subgroupOf ((M ⊔ conjugate M a) ⊓ centralizer ({a} : Set G))) :=
      CatalogueBAlternating.pComponent_perfect hT
    have h2 : Group.IsPerfect ↥T :=
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hTK).toMonoidHom)
        (subgroupOfEquivOfLe hTK).surjective
    exact Subgroup.isPerfect_iff.mp h2
  have hT₁perf : ⁅T.subgroupOf H, T.subgroupOf H⁆ = T.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hTH, hTperf]
  have hTnt : (T.subgroupOf H).map π ≠ ⊥ := by
    intro hbot
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    have hTodd : Nat.Coprime 2 (Nat.card T) := by
      have h1 : Nat.card (T.subgroupOf H) ∣ Nat.card (pPrimeCore 2 ↥H) := card_dvd_of_le hbot
      rw [Nat.card_congr (subgroupOfEquivOfLe hTH).toEquiv] at h1
      exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
    have htop : pPrimeCore 2 ↥T = ⊤ :=
      top_unique (le_sSup ⟨inferInstance, by rwa [card_top]⟩)
    have hq : IsQuasisimple (↥T ⧸ pPrimeCore 2 ↥T) :=
      ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 T _ hTK).mp hT).2.2
    have hnt : Nontrivial (↥T ⧸ pPrimeCore 2 ↥T) := LocalCores.isQuasisimple_nontrivial hq
    have h1 : Nat.card (↥T ⧸ pPrimeCore 2 ↥T) = 1 := by
      rw [← index_eq_card, htop, index_top]
    exact (Finite.one_lt_card_iff_nontrivial.mpr hnt).ne' h1
  have hmain : ⁅(M.subgroupOf H).map π, (S.subgroupOf H).map π⁆ = (M.subgroupOf H).map π := by
    set A := (M.subgroupOf H).map π with hAdef
    set Sb := (S.subgroupOf H).map π with hSbdef
    have hSbA : Sb ≤ normalizer (A : Set (↥H ⧸ pPrimeCore 2 ↥H)) :=
      (map_mono hS₁M).trans (le_normalizer_map π)
    have hD : ⁅A, Sb⁆ ≤ A := UnbalancedLayer.commutator_le_left_of_le_normalizer hSbA
    have hDn : ((⁅A, Sb⁆ : Subgroup (↥H ⧸ pPrimeCore 2 ↥H)).subgroupOf A).Normal :=
      (normal_subgroupOf_iff_le_normalizer hD).mpr (normalizer_commutator_ge_left A Sb)
    rcases LocalCores.quasisimple_normal_subgroups hAq hDn with htop | hcen
    · exact le_antisymm hD (subgroupOf_eq_top.mp htop)
    · exfalso
      have hD1 : ⁅A, Sb⁆ = ⊥ := by
        apply LocalCores.perfect_double_commutator hAq.1
        rw [commutator_eq_bot_iff_le_centralizer]
        intro x hx
        rw [mem_centralizer_iff]
        intro y hy
        have hxc := hcen (show (⟨x, hD hx⟩ : A) ∈ (⁅A, Sb⁆ : Subgroup _).subgroupOf A from hx)
        exact congrArg Subtype.val (mem_center_iff.mp hxc ⟨y, hy⟩)
      set Tb := (T.subgroupOf H).map π with hTbdef
      set a' : H := ⟨a, haH⟩ with ha'def
      have hTbSb : Tb ≤ Sb := map_mono (fun y hy => hTS hy)
      have hTbA : ∀ t ∈ Tb, ∀ u ∈ A, u * t = t * u := by
        intro t ht u hu
        have h1 := commutator_mem_commutator hu (hTbSb ht)
        rw [hD1, mem_bot] at h1
        exact commutatorElement_eq_one_iff_mul_comm.mp h1
      have hTba : ∀ t ∈ Tb, t * π a' = π a' * t := by
        rintro _ ⟨y, hy, rfl⟩
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (mem_centralizer_singleton_iff.mp (hTC hy))
      have hTbA' : ∀ t ∈ Tb, ∀ u ∈ ((conjugate M a).subgroupOf H).map π, u * t = t * u := by
        intro t ht u hu
        obtain ⟨x, hx, rfl⟩ := hu
        have hx' : a' * x * a'⁻¹ ∈ M.subgroupOf H := by
          rw [mem_subgroupOf]
          exact (UnbalancedLayer.mem_conjugate_iff.mp hx)
        have hw := hTbA t ht _ (mem_map_of_mem π hx')
        rw [map_mul, map_mul, map_inv] at hw
        have hta := hTba t ht
        calc π x * t = (π a')⁻¹ * (π a' * π x * (π a')⁻¹) * π a' * t := by group
          _ = (π a')⁻¹ * (π a' * π x * (π a')⁻¹) * (π a' * t) := by group
          _ = (π a')⁻¹ * (π a' * π x * (π a')⁻¹) * (t * π a') := by rw [hta]
          _ = (π a')⁻¹ * ((π a' * π x * (π a')⁻¹) * t) * π a' := by group
          _ = (π a')⁻¹ * (t * (π a' * π x * (π a')⁻¹)) * π a' := by rw [hw]
          _ = ((π a')⁻¹ * t) * (π a' * π x * (π a')⁻¹) * π a' := by group
          _ = (t * (π a')⁻¹) * (π a' * π x * (π a')⁻¹) * π a' := by
            rw [show (π a')⁻¹ * t = t * (π a')⁻¹ by
              rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hta, mul_assoc, mul_inv_cancel, mul_one]]
          _ = t * π x := by group
      have hKmap : (K.subgroupOf H).map π =
          A ⊔ ((conjugate M a).subgroupOf H).map π := by
        rw [hKdef, subgroupOf_sup hMH hMaH, Subgroup.map_sup]
      have hcen' : (K.subgroupOf H).map π ≤ centralizer (Tb : Set (↥H ⧸ pPrimeCore 2 ↥H)) := by
        rw [hKmap]
        refine sup_le (fun u hu => ?_) (fun u hu => ?_)
        · rw [mem_centralizer_iff]
          intro t ht
          exact (hTbA t ht u hu).symm
        · rw [mem_centralizer_iff]
          intro t ht
          exact (hTbA' t ht u hu).symm
      have hTbK : Tb ≤ (K.subgroupOf H).map π := map_mono (fun y hy => hTKk hy)
      apply hTnt
      refine eq_bot_of_perfect_of_comm (by rw [hTbdef, ← map_commutator, hT₁perf]) ?_
      intro x hx y hy
      exact mem_centralizer_iff.mp (hcen' (hTbK hy)) x hx
  have hMS₁ := le_of_commutator_map_eq hM hS₁M hM₁S hmain
  have hMS : M ≤ S := fun y hy => hMS₁ (show (⟨y, hMH hy⟩ : H) ∈ M.subgroupOf H from hy)
  have hMaS : conjugate M a ≤ S := by
    rw [← UnbalancedLayer.conjugate_eq_of_mem_normalizer haS]
    exact map_mono hMS
  exact le_antisymm hSK (sup_le hMS hMaS)

end CFSG.ComponentClassification.UnbalancedCorr

section KGroup

namespace CFSG.ComponentClassification.UnbalancedCorr

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem normalizer_ne_top_of_isSimpleGroup [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x)
    {B : Subgroup G} (hB1 : B ≠ ⊥) (hB : IsPGroup 2 B) : normalizer (B : Set G) ≠ ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro htop
  have hBn : B.Normal := normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal B with h | h
  · exact hB1 h
  · obtain ⟨x, y, hxy⟩ := hnonab
    have hG : IsPGroup 2 G := by
      rw [h] at hB
      exact hB.of_equiv Subgroup.topEquiv
    have : Nontrivial G := ⟨⟨x * y, y * x, hxy⟩⟩
    have hZ := hG.center_nontrivial
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with hz | hz
    · rw [hz] at hZ
      exact (Subgroup.nontrivial_iff_ne_bot ⊥).mp hZ rfl
    · have hy : y ∈ center G := by rw [hz]; exact mem_top y
      exact hxy (mem_center_iff.mp hy x)

theorem isKGroupCat_of_ne_top (hK : Assembly.KProper Blueprint.Catalog G) {H : Subgroup G}
    (hH : H ≠ ⊤) : SectionRank.IsKGroupCat ↥H :=
  UnbalancingLocal.kGroupOver_of_kProper (fun e h => SectionRank.catalog_of_mulEquiv e h)
    (fun S _ _ _ hcomm => UnbalancingLocal.catalog_of_abelian_simple S hcomm) hK H hH

theorem le_pLayer_of_isPComponent_centralizer
    (hS : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    {H : Subgroup G} (hK : SectionRank.IsKGroupCat ↥H) {a : G} (haH : a ∈ H)
    (ha : orderOf a = 2) {T : Subgroup G} (hT : T ≤ centralizer ({a} : Set G) ⊓ H)
    (hTpc : IsPComponent 2 (T.subgroupOf (centralizer ({a} : Set G) ⊓ H))) :
    T ≤ (pLayer ↥H 2).map H.subtype := by
  have ha' : orderOf (⟨a, haH⟩ : H) = 2 := by rw [Subgroup.orderOf_mk]; exact ha
  have hcena := UGSChain.centralizer_mk_eq_subgroupOf haH
  have hT'C : T.subgroupOf H ≤ centralizer ({(⟨a, haH⟩ : H)} : Set H) := by
    rw [hcena]
    intro y hy
    exact mem_subgroupOf.mpr (hT (mem_subgroupOf.mp hy))
  have hT'pc : IsPComponent 2 ((T.subgroupOf H).subgroupOf
      (centralizer ({(⟨a, haH⟩ : H)} : Set H))) := by
    rw [hcena, isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2 Nat.prime_two]
    exact hTpc
  have h := (UGSChain.kGroup_involution_fixed_two_layer_containment_of_schreier hS hK ha').1
    _ hT'C hT'pc
  intro t ht
  exact ⟨⟨t, (hT ht).2⟩, h (show (⟨t, (hT ht).2⟩ : H) ∈ T.subgroupOf H from ht), rfl⟩

end CFSG.ComponentClassification.UnbalancedCorr

end KGroup
