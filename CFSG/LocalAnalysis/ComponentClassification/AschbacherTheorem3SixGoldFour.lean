module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixGoldThree
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightBenderCase

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.SignalizerFunctor.Helpers
open CFSG.Open
open scoped Pointwise commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem bender_center {L P : Subgroup X} {n : ℕ} (hB : IsBenderType L n)
    (hP : IsSylowOf 2 P L) :
    (∀ x ∈ P ⊓ Subgroup.centralizer (P : Set X), x ^ 2 = 1) ∧
    Nat.card (P ⊓ Subgroup.centralizer (P : Set X) : Subgroup X) = 2 ^ n := by
  obtain ⟨k, -, hBB, -⟩ := FourEight.exists_benderBorel hB
  obtain ⟨Q, hQ⟩ := hP
  obtain ⟨-, -, hZ2, hZcard, -⟩ := hBB Q
  set ψ : (Q : Subgroup L) →* X := L.subtype.comp (Q : Subgroup L).subtype with hψ
  have hψinj : Function.Injective ψ := L.subtype_injective.comp (Q : Subgroup L).subtype_injective
  have hψQ : (⊤ : Subgroup (Q : Subgroup L)).map ψ = P := by
    rw [← hQ, hψ, ← Subgroup.map_map, map_subtype_top]
  have hZ : (Subgroup.center (Q : Subgroup L)).map ψ = P ⊓ Subgroup.centralizer (P : Set X) := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [← hψQ]
        exact Subgroup.mem_map_of_mem ψ (Subgroup.mem_top q)
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [← hψQ] at hy
        obtain ⟨q', -, rfl⟩ := hy
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hq q')]
    · rintro ⟨hxP, hxC⟩
      rw [← hψQ] at hxP
      obtain ⟨q, -, rfl⟩ := hxP
      refine ⟨q, Subgroup.mem_center_iff.mpr fun q' => hψinj ?_, rfl⟩
      rw [map_mul, map_mul]
      have hq' : ψ q' ∈ P := by
        rw [← hψQ]
        exact Subgroup.mem_map_of_mem ψ (Subgroup.mem_top q')
      exact Subgroup.mem_centralizer_iff.mp hxC _ hq'
  refine ⟨?_, ?_⟩
  · rw [← hZ]
    rintro _ ⟨q, hq, rfl⟩
    rw [← map_pow, hZ2 q hq, map_one]
  · rw [← hZ, Subgroup.card_map_of_injective hψinj, hZcard]

namespace Conf46

variable {G T S Q H : Subgroup X} {g : X}

theorem simple_G (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤) (hO : CFSG.oddCore G = ⊥)
    (IH : IH46 (Nat.card (G ⊔ T : Subgroup X)))
    (hnn : ∀ D : Subgroup X, omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ D → D ≤ S ⊓ G →
      G ≤ Subgroup.normalizer (D : Set X) → False)
    (hG : CFSG.Goldschmidt.TopStatement) (hK : GoldschmidtTypeAutomorphisms)
    (hMG : Subgroup.normalClosure (omegaOne ((T ⊔ rightConjugate T g) ⊓ G) : Set X) = G) :
    IsSimpleGroup G ∧ goldschmidtSimpleType (G ⧸ Subgroup.center G) ∧
    Subgroup.center G = ⊥ ∧ pCoreOf 2 G = ⊥ ∧
    omegaOne ((T ⊔ rightConjugate T g) ⊓ G) = omegaOne (S ⊓ G) := by
  have hC0 := c.pCoreOf_eq_bot htop hO IH hnn hG hK hMG
  have hGn : G.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le Subgroup.le_normalizer c.frame.le_normalizer
  set C := pCoreOf 2 G with hCdef
  have hCn : C.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    exact (Subgroup.normalizer_eq_top_iff.mpr hGn).symm.le.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 G)
  obtain ⟨hsimp, htype⟩ := c.simple_bar htop hO IH hnn hG hMG hCdef
  obtain ⟨-, -, -, hZeq, -⟩ := c.goldschmidt_one htop hO IH hnn hG hMG
  have hinj : Function.Injective (QuotientGroup.mk' C) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hC0]
  set e : G ≃* G.map (QuotientGroup.mk' C) := G.equivMapOfInjective _ hinj with he
  have hpc : CFSG.Open.pCore 2 G = ⊥ := by
    have h1 : (CFSG.Open.pCore 2 G).map G.subtype = ⊥ := hC0
    exact (Subgroup.map_eq_bot_iff_of_injective _ G.subtype_injective).mp h1
  refine ⟨e.isSimpleGroup, goldschmidtSimpleType_of_mulEquiv
    (QuotientGroup.congr (Subgroup.center G) (Subgroup.center _) e (Subgroup.map_center_eq e))
    htype, center_eq_bot_of_cores hO hpc, hC0, ?_⟩
  rw [hZeq, ← hCdef, hC0, bot_sup_eq]

theorem inner_decomp (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤) (hO : CFSG.oddCore G = ⊥)
    (IH : IH46 (Nat.card (G ⊔ T : Subgroup X)))
    (hnn : ∀ D : Subgroup X, omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ D → D ≤ S ⊓ G →
      G ≤ Subgroup.normalizer (D : Set X) → False)
    (hG : CFSG.Goldschmidt.TopStatement) (hK : GoldschmidtTypeAutomorphisms)
    (hMG : Subgroup.normalClosure (omegaOne ((T ⊔ rightConjugate T g) ⊓ G) : Set X) = G) :
    omegaOne (T ⊔ rightConjugate T g) = omegaOne T ⊔
      (omegaOne (T ⊔ rightConjugate T g) ⊓ Subgroup.centralizer (G : Set X)) ∧
    omegaOne (T ⊔ rightConjugate T g) = omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ⊔
      (omegaOne (T ⊔ rightConjugate T g) ⊓ Subgroup.centralizer (G : Set X)) ∧
    omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ⊓
      (omegaOne (T ⊔ rightConjugate T g) ⊓ Subgroup.centralizer (G : Set X)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsimp, htype, hcen, -, hZS⟩ := c.simple_G htop hO IH hnn hG hK hMG
  obtain ⟨-, hperf, -, -, -⟩ := c.goldschmidt_one htop hO IH hnn hG hMG
  set Z₁ := omegaOne ((T ⊔ rightConjugate T g) ⊓ G) with hZ₁def
  set U := omegaOne T with hUdef
  set V := omegaOne (T ⊔ rightConjugate T g) with hVdef
  have hVeq : V = U ⊔ Z₁ := c.omegaOne_W
  have hVab : IsMulCommutative V := isMulCommutative_of_le (omegaOne_le _) c.isMulCommutative_W
  have hVel : IsElemAbelian 2 V :=
    ⟨hVab, fun v hv => ((mem_omegaOne_iff c.isMulCommutative_W).mp hv).2⟩
  have hVS : V ≤ S := (omegaOne_le _).trans c.W_le_S
  have hGn : G.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le Subgroup.le_normalizer c.frame.le_normalizer
  have hVG : V ≤ Subgroup.normalizer (G : Set X) := fun _ _ => by
    rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top _
  have hVP : V ≤ Subgroup.normalizer ((S ⊓ G : Subgroup X) : Set X) := fun v hv =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hVS hv), hVG hv⟩
  have hZV : Z₁ ≤ V := by rw [hVeq]; exact le_sup_right
  have hUV : U ≤ V := by rw [hVeq]; exact le_sup_left
  have hVc : ∀ e ∈ V, ∀ x ∈ omegaOne (S ⊓ G), e * x = x * e := by
    intro e he x hx
    rw [← hZS] at hx
    exact congrArg Subtype.val (hVab.is_comm.comm ⟨e, he⟩ ⟨x, hZV hx⟩)
  have hVcomm : ∀ e ∈ V, ∀ p ∈ S ⊓ G, e⁻¹ * p⁻¹ * e * p ∈ omegaOne (S ⊓ G) := by
    intro e he p hp
    rw [← hZS]
    exact c.commutator_mem_omegaOne_W he hp.1
  have hbound := hK X G (S ⊓ G) V hsimp htype c.isSylowOf_inf hVel hVG hVP hVc hVcomm
  rw [← hZS] at hbound
  set Cen := V ⊓ Subgroup.centralizer (G : Set X) with hCendef
  have hCenN : ∀ K ≤ V, Cen ≤ Subgroup.normalizer (K : Set X) := by
    intro K hKV
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hVab.is_comm.comm ⟨y, hKV hy⟩ ⟨x, hx.1⟩)
  have hUCen : U ⊓ Cen = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨hu, -, hc⟩
    rw [Subgroup.mem_bot]
    refine c.eq_one_of_commutator_le (C := ⊥) hperf bot_le (omegaOne_le T hu) ?_
    rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff,
      Subgroup.zpowers_le]
    exact hc
  have hZCen : Z₁ ⊓ Cen = ⊥ := by
    rw [eq_bot_iff]
    rintro d ⟨hdZ, -, hdC⟩
    have hdG : d ∈ G := ((omegaOne_le _).trans inf_le_right) hdZ
    have hdc : d ∈ (Subgroup.center G).map G.subtype :=
      (CFSG.LocalCores.mem_map_center_iff G).mpr ⟨hdG, hdC⟩
    rwa [hcen, Subgroup.map_bot] at hdc
  have hZU : Nat.card Z₁ = Nat.card U := c.card_omegaOne_Z
  have hVUC : V = U ⊔ Cen := by
    refine (Subgroup.eq_of_le_of_card_ge (sup_le hUV inf_le_left) ?_).symm
    rw [card_sup_of_le_normalizer (hCenN U hUV) hUCen, ← hZU]
    exact hbound
  have hVZC : V = Z₁ ⊔ Cen := by
    refine (Subgroup.eq_of_le_of_card_ge (sup_le hZV inf_le_left) ?_).symm
    rw [card_sup_of_le_normalizer (hCenN Z₁ hZV) hZCen]
    exact hbound
  exact ⟨hVUC, hVZC, hZCen⟩

theorem exists_inner (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤) (hO : CFSG.oddCore G = ⊥)
    (IH : IH46 (Nat.card (G ⊔ T : Subgroup X)))
    (hnn : ∀ D : Subgroup X, omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ D → D ≤ S ⊓ G →
      G ≤ Subgroup.normalizer (D : Set X) → False)
    (hG : CFSG.Goldschmidt.TopStatement) (hK : GoldschmidtTypeAutomorphisms)
    (hMG : Subgroup.normalClosure (omegaOne ((T ⊔ rightConjugate T g) ⊓ G) : Set X) = G)
    {z : X} (hz : z ∈ omegaOne ((T ⊔ rightConjugate T g) ⊓ G)) :
    ∃ u ∈ omegaOne T, (z ≠ 1 → u ≠ 1) ∧ ∀ x ∈ G, u * x * u⁻¹ = z * x * z⁻¹ := by
  obtain ⟨hVUC, -, hZCen⟩ := c.inner_decomp htop hO IH hnn hG hK hMG
  set Z₁ := omegaOne ((T ⊔ rightConjugate T g) ⊓ G) with hZ₁def
  set U := omegaOne T with hUdef
  set V := omegaOne (T ⊔ rightConjugate T g) with hVdef
  set Cen := V ⊓ Subgroup.centralizer (G : Set X) with hCendef
  have hVab : IsMulCommutative V := isMulCommutative_of_le (omegaOne_le _) c.isMulCommutative_W
  have hVeq : V = U ⊔ Z₁ := c.omegaOne_W
  have hUV : U ≤ V := by rw [hVeq]; exact le_sup_left
  have hZV : Z₁ ≤ V := by rw [hVeq]; exact le_sup_right
  have hCenN : Cen ≤ Subgroup.normalizer (U : Set X) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hVab.is_comm.comm ⟨y, hUV hy⟩ ⟨x, hx.1⟩)
  have hzm : z ∈ (U : Set X) * (Cen : Set X) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hCenN, ← hVUC]
    exact hZV hz
  obtain ⟨u, hu, d, hd, rfl⟩ := Set.mem_mul.mp hzm
  refine ⟨u, hu, fun hz1 hu1 => hz1 ?_, fun x hx => ?_⟩
  · rw [hu1, one_mul] at hz ⊢
    have h1 : d ∈ Z₁ ⊓ Cen := ⟨hz, hd⟩
    rwa [hZCen, Subgroup.mem_bot] at h1
  · have hdx : d * x = x * d := (Subgroup.mem_centralizer_iff.mp hd.2 x hx).symm
    calc u * x * u⁻¹ = u * (x * d * d⁻¹) * u⁻¹ := by group
      _ = u * (d * x * d⁻¹) * u⁻¹ := by rw [hdx]
      _ = u * d * x * (u * d)⁻¹ := by group

theorem bender_of_eq (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤) (hO : CFSG.oddCore G = ⊥)
    (IH : IH46 (Nat.card (G ⊔ T : Subgroup X)))
    (hnn : ∀ D : Subgroup X, omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ D → D ≤ S ⊓ G →
      G ≤ Subgroup.normalizer (D : Set X) → False)
    (hG : CFSG.Goldschmidt.TopStatement) (hK : Theorem3KnownGroupFacts)
    (hMG : Subgroup.normalClosure (omegaOne ((T ⊔ rightConjugate T g) ⊓ G) : Set X) = G) :
    Bender46 G T S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKa := hK.goldschmidt_type_automorphisms
  obtain ⟨hsimp, htype, hcen, hC0, hZS⟩ := c.simple_G htop hO IH hnn hG hKa hMG
  obtain ⟨-, hperf, -, -, -⟩ := c.goldschmidt_one htop hO IH hnn hG hMG
  obtain ⟨-, hVZC, -⟩ := c.inner_decomp htop hO IH hnn hG hKa hMG
  set Z₁ := omegaOne ((T ⊔ rightConjugate T g) ⊓ G) with hZ₁def
  set U := omegaOne T with hUdef
  set V := omegaOne (T ⊔ rightConjugate T g) with hVdef
  set P := S ⊓ G with hPdef
  have hPsyl : IsSylowOf 2 P G := c.isSylowOf_inf
  have hGn : G.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le Subgroup.le_normalizer c.frame.le_normalizer
  have hBen : ∃ n : ℕ, IsBenderType G n := by
    rcases hK.goldschmidt_type_generation X G P hsimp htype hPsyl with hB | hgen
    · exact hB
    · exfalso
      apply c.hyp45.facts.1
      have hle : (⨆ z : {z : X // z ∈ P ∧ z ^ 2 = 1 ∧ z ≠ 1},
          G ⊓ Subgroup.centralizer {(z : X)}) ≤ H := by
        refine iSup_le fun ⟨z, hzP, hz2, hz1⟩ => ?_
        have hzZ : z ∈ Z₁ := hZS ▸ mem_omegaOne hzP hz2
        obtain ⟨u, hu, hu1, hux⟩ := c.exists_inner htop hO IH hnn hG hKa hMG hzZ
        rintro y ⟨hyG, hyC⟩
        apply c.hyp43.centralizer_le c.frame (omegaOne_le T hu) (hu1 hz1)
        refine ⟨Subgroup.mem_sup_left hyG, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
        have h1 := hux y hyG
        have h2 : z * y * z⁻¹ = y := by rw [← hyz, mul_inv_cancel_right]
        rw [h2] at h1
        calc y * u = (u * y * u⁻¹) * u := by rw [h1]
          _ = u * y := by group
      exact hle (hgen c.mem)
  obtain ⟨n, hB⟩ := hBen
  obtain ⟨⟨z₀, hz₀Z⟩, hz₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp c.omegaOne_Z_ne_bot
  have hz₀1' : z₀ ≠ 1 := fun h => hz₀1 (Subtype.ext h)
  obtain ⟨u₀, hu₀, hu₀1, hu₀x⟩ := c.exists_inner htop hO IH hnn hG hKa hMG hz₀Z
  have hz₀P : z₀ ∈ P := omegaOne_le _ (hZS ▸ hz₀Z)
  have hz₀2 : z₀ ^ 2 = 1 :=
    ((mem_omegaOne_iff (isMulCommutative_of_le inf_le_left c.isMulCommutative_W)).mp hz₀Z).2
  have hz₀c := (FourEight.bender_sylow hB hPsyl).1 z₀ hz₀P hz₀2
  have hPu : P ≤ S ⊓ Subgroup.centralizer {u₀} := by
    intro p hp
    refine ⟨hp.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := hu₀x p hp.2
    have h2 : z₀ * p * z₀⁻¹ = p := by rw [hz₀c p hp, mul_inv_cancel_right]
    rw [h2] at h1
    calc p * u₀ = (u₀ * p * u₀⁻¹) * u₀ := by rw [h1]
      _ = u₀ * p := by group
  have hPH : P ≤ H ⊓ S := by
    rw [lemma_4_5_one c.hyp45 (omegaOne_le T hu₀) (hu₀1 hz₀1')]
    exact hPu
  have hPT : P ≤ Subgroup.centralizer (T : Set X) := hPH.trans c.hyp45.le_centralizer
  have hPTg : P ≤ Subgroup.centralizer (rightConjugate T g : Set X) := by
    have h1 := hPH
    rw [lemma_4_5_two c.hyp45] at h1
    exact h1.trans inf_le_right
  have hWP : T ⊔ rightConjugate T g ≤ Subgroup.centralizer (P : Set X) :=
    sup_le (Subgroup.le_centralizer_iff.mp hPT) (Subgroup.le_centralizer_iff.mp hPTg)
  have hZP : (T ⊔ rightConjugate T g) ⊓ G ≤ P ⊓ Subgroup.centralizer (P : Set X) :=
    le_inf (le_inf (inf_le_left.trans c.W_le_S) inf_le_right) (inf_le_left.trans hWP)
  obtain ⟨hZel, hZcard⟩ := bender_center hB hPsyl
  have hTsq : ∀ t ∈ T, t ^ 2 = 1 := by
    intro t ht
    have htg : g⁻¹ * t * g ∈ rightConjugate T g := conj_mem_rightConjugate ht g
    have hw : t⁻¹ * (g⁻¹ * t * g) ∈ (T ⊔ rightConjugate T g) ⊓ G := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.mem_sup_left (T.inv_mem ht))
        (Subgroup.mem_sup_right htg), ?_⟩
      have h1 : t⁻¹ * (g⁻¹ * t * g) = (t⁻¹ * g⁻¹ * t) * g := by group
      have h2 : t⁻¹ * g⁻¹ * t ∈ G := by
        have := hGn.conj_mem g⁻¹ (G.inv_mem c.mem) t⁻¹
        simpa using this
      rw [h1]
      exact G.mul_mem h2 c.mem
    have h1 := hZel _ (hZP hw)
    have hcomm : Commute t⁻¹ (g⁻¹ * t * g) := congrArg Subtype.val
      (c.isMulCommutative_W.is_comm.comm ⟨t⁻¹, Subgroup.mem_sup_left (T.inv_mem ht)⟩
        ⟨_, Subgroup.mem_sup_right htg⟩)
    have hconj : (g⁻¹ * t * g) ^ 2 = g⁻¹ * t ^ 2 * g := by rw [pow_two, pow_two]; group
    rw [hcomm.mul_pow, inv_pow, hconj] at h1
    have h2 : g⁻¹ * t ^ 2 * g = t ^ 2 := by
      calc g⁻¹ * t ^ 2 * g = (t ^ 2)⁻¹⁻¹ * ((t ^ 2)⁻¹ * (g⁻¹ * t ^ 2 * g)) := by group
        _ = t ^ 2 := by rw [h1, mul_one, inv_inv]
    have h3 : t ^ 2 ∈ T ⊓ rightConjugate T g := by
      refine ⟨T.pow_mem ht 2, ?_⟩
      rw [← h2]
      exact conj_mem_rightConjugate (T.pow_mem ht 2) g
    rw [c.hyp45.facts.2.1, Subgroup.mem_bot] at h3
    exact h3
  have hTel : IsElemAbelian 2 T := ⟨c.isMulCommutative, hTsq⟩
  have hUT : U = T := le_antisymm (omegaOne_le T) (le_omegaOne hTsq)
  have hΩZ : omegaOne P = P ⊓ Subgroup.centralizer (P : Set X) := by
    apply le_antisymm
    · rw [omegaOne, Subgroup.closure_le]
      rintro x ⟨hxP, hx2⟩
      refine ⟨hxP, Subgroup.mem_centralizer_iff.mpr fun p hp => ?_⟩
      exact ((FourEight.bender_sylow hB hPsyl).1 x hxP hx2 p hp).symm
    · intro x hx
      exact mem_omegaOne hx.1 (hZel x hx)
  have hcardT : Nat.card T = 2 ^ n := by
    have hZU : Nat.card Z₁ = Nat.card U := c.card_omegaOne_Z
    rw [← hUT, ← hZU, hZS, hΩZ, hZcard]
  set A := Subgroup.centralizer (G : Set X) with hAdef
  have hAG : A ⊓ G = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, hxG⟩
    have h1 : x ∈ (Subgroup.center G).map G.subtype :=
      (CFSG.LocalCores.mem_map_center_iff G).mpr ⟨hxG, hxA⟩
    rwa [hcen, Subgroup.map_bot] at h1
  have hTA : T ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    rintro t ⟨ht, htA⟩
    rw [Subgroup.mem_bot]
    refine c.eq_one_of_commutator_le (C := ⊥) hperf bot_le ht ?_
    rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff,
      Subgroup.zpowers_le]
    exact htA
  have hTAG : T ≤ A ⊔ G := by
    intro t ht
    have htU : t ∈ U := by rw [hUT]; exact ht
    have htV : t ∈ V := omegaOne_mono le_sup_left htU
    rw [hVZC] at htV
    exact (sup_le (((omegaOne_le _).trans inf_le_right).trans le_sup_right)
      (inf_le_right.trans le_sup_left)) htV
  have hXAG : A ⊔ G = ⊤ := by
    rw [eq_top_iff, ← htop]
    exact sup_le le_sup_right hTAG
  set ρ := QuotientGroup.mk' G with hρ
  have hρT : ∀ x : X, ∃ t ∈ T, ρ x = ρ t := by
    intro x
    have hx : x ∈ G ⊔ T := htop ▸ Subgroup.mem_top x
    obtain ⟨t, ht, y, hy, rfl⟩ := c.frame.mem_sup_iff.mp hx
    refine ⟨t, ht, ?_⟩
    have h1 : ρ y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
    rw [map_mul, h1, mul_one]
  have hAsq : ∀ a ∈ A, a ^ 2 = 1 := by
    intro a ha
    obtain ⟨t, ht, hat⟩ := hρT a
    have h1 : a ^ 2 ∈ G := by
      apply (QuotientGroup.eq_one_iff _).mp
      show ρ (a ^ 2) = 1
      rw [map_pow, hat, ← map_pow, hTsq t ht, map_one]
    have h2 : a ^ 2 ∈ A ⊓ G := ⟨A.pow_mem ha 2, h1⟩
    rwa [hAG, Subgroup.mem_bot] at h2
  have hAab : IsMulCommutative A := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨t, ht, hat⟩ := hρT a
    obtain ⟨t', ht', hbt⟩ := hρT b
    have h1 : ⁅(a : X), (b : X)⁆ ∈ G := by
      apply (QuotientGroup.eq_one_iff _).mp
      show ρ ⁅(a : X), (b : X)⁆ = 1
      rw [map_commutatorElement, hat, hbt, ← map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm.mpr (congrArg Subtype.val
          (c.isMulCommutative.is_comm.comm ⟨t, ht⟩ ⟨t', ht'⟩)), map_one]
    have hA' : ⁅(a : X), (b : X)⁆ ∈ A := by
      rw [commutatorElement_def]
      exact A.mul_mem (A.mul_mem (A.mul_mem a.2 b.2) (A.inv_mem a.2)) (A.inv_mem b.2)
    have h2 : ⁅(a : X), (b : X)⁆ ∈ A ⊓ G := ⟨hA', h1⟩
    rw [hAG, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2
  have hA2 : IsPGroup 2 A := fun a => ⟨1, Subtype.ext (by simpa using hAsq a a.2)⟩
  have hAcard : Nat.card A = 2 ^ n := by
    have hAn : A.Normal := inferInstance
    have h1 := card_sup_of_le_normalizer (A := A) (B := G)
      (fun _ _ => by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top _) hAG
    have h2 := card_sup_of_le_normalizer c.frame.le_normalizer
      (by rw [inf_comm]; exact c.frame.inf_eq_bot)
    rw [hXAG] at h1
    rw [htop] at h2
    rw [← hcardT]
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := G))
    rw [← h1, h2, mul_comm]
  have hTG : ⁅T, G⁆ = G := by
    have hle : ⁅T, G⁆ ≤ G := commutator_le_of_le_normalizer c.frame.le_normalizer
    have hn : (⁅T, G⁆.subgroupOf G).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (Subgroup.normalizer_commutator_ge_right T G)
    rcases hn.eq_bot_or_eq_top with hbot | htop'
    · exfalso
      have hTG0 : ⁅T, G⁆ = ⊥ := by
        rw [Subgroup.subgroupOf_eq_bot] at hbot
        have h1 := disjoint_iff.mp hbot
        rwa [inf_eq_left.mpr hle] at h1
      apply c.ne_bot
      rw [eq_bot_iff, ← hTA]
      exact le_inf le_rfl (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hTG0)
    · exact le_antisymm hle ((Subgroup.subgroupOf_eq_top).mp htop')
  have hcc : conjugateClosure G T = ⊤ := by
    rw [FourEight.conjugateClosure_eq, hTG, sup_comm, htop]
  have hO2 : pCoreOf 2 (⊤ : Subgroup X) = A := by
    apply le_antisymm
    · set O := pCoreOf 2 (⊤ : Subgroup X) with hOdef
      have hO2' : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤
      have hON : (⊤ : Subgroup X) ≤ Subgroup.normalizer (O : Set X) :=
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 ⊤
      have hOG : O ⊓ G ≤ pCoreOf 2 G :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
          (fun x _ => Subgroup.inf_normalizer_le_normalizer_inf
            ⟨hON (Subgroup.mem_top x), by
              rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x⟩)
          (hO2'.to_le inf_le_left)
      rw [hC0, le_bot_iff] at hOG
      have hcomm : ⁅O, G⁆ = ⊥ := by
        rw [eq_bot_iff, ← hOG]
        exact le_inf ((Subgroup.le_normalizer_iff_commutator_le_left).mp (le_top.trans hON))
          ((Subgroup.le_normalizer_iff_commutator_le_right).mp
            (fun x _ => by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x))
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_top
        (fun x _ => by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x) hA2
  unfold Bender46
  rw [hcc, hO2, hTG]
  exact ⟨n, hXAG.symm, hAG, Subgroup.commutator_eq_bot_iff_le_centralizer.mpr le_rfl, ⟨hAab, hAsq⟩,
    hAcard, hB, hTel, hcardT, inf_le_right, hTA⟩

end Conf46

end CFSG.ComponentClassification.AschbacherTheorem3
