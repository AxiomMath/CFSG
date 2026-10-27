module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBaumannTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellUtil
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellSeed
public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2

section BaumannIn

variable {G : Type*} [Group G]

@[expose] def elemBaumannIn (p : ℕ) (R : Subgroup G) : Subgroup G :=
  (elemBaumann R p).map R.subtype

theorem mem_elemBaumannIn_iff {p : ℕ} {R : Subgroup G} {x : G} [Finite G] [Fact p.Prime] :
    x ∈ elemBaumannIn p R ↔ x ∈ R ∧ ∀ e ∈ elemCenterIn p R, e * x = x * e := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hy e he))
  · rintro ⟨hxR, hx⟩
    refine ⟨⟨x, hxR⟩, ?_, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr fun e he => ?_
    exact Subtype.ext (hx e ⟨e, he, rfl⟩)

theorem elemBaumannIn_le (p : ℕ) (R : Subgroup G) : elemBaumannIn p R ≤ R := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem mem_elemCenterIn_iff_centralizer {p : ℕ} {R : Subgroup G} {x : G} [Finite G] [Fact p.Prime] :
    x ∈ elemCenterIn p R ↔ x ∈ R ∧ x ^ p = 1 ∧ ∀ j ∈ elemThompsonIn p R, j * x = x * j := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hc, hp⟩ := mem_elemThompsonCenterTorsion_iff_centralizer.mp hy
    refine ⟨y.2, by simpa using congrArg Subtype.val hp, ?_⟩
    rintro _ ⟨j, hj, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc j hj)
  · rintro ⟨hxR, hxp, hxj⟩
    refine ⟨⟨x, hxR⟩, mem_elemThompsonCenterTorsion_iff_centralizer.mpr ⟨?_, ?_⟩, rfl⟩
    · refine Subgroup.mem_centralizer_iff.mpr fun j hj => ?_
      exact Subtype.ext (hxj j ⟨j, hj, rfl⟩)
    · exact Subtype.ext (by simpa using hxp)

theorem elemThompsonIn_le (p : ℕ) (R : Subgroup G) : elemThompsonIn p R ≤ R := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem le_normalizer_elemCenterIn [Finite G] (p : ℕ) [Fact p.Prime] (R : Subgroup G) :
    R ≤ Subgroup.normalizer ((elemCenterIn p R : Subgroup G) : Set G) := by
  have key : ∀ r ∈ R, ∀ x ∈ elemCenterIn p R, r * x * r⁻¹ ∈ elemCenterIn p R := by
    intro r hr x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 := Subgroup.mem_comap.mp
      (Subgroup.characteristic_iff_le_comap.mp (elemThompsonCenterTorsion_characteristic R p)
        (MulAut.conj (⟨r, hr⟩ : R)) hy)
    exact ⟨_, h1, by simp⟩
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨key r hr x, fun hx => by simpa [mul_assoc] using key r⁻¹ (R.inv_mem hr) _ hx⟩

theorem elemThompsonIn_le_elemBaumannIn [Finite G] (p : ℕ) [Fact p.Prime] (R : Subgroup G) :
    elemThompsonIn p R ≤ elemBaumannIn p R := by
  rintro _ ⟨j, hj, rfl⟩
  refine ⟨j, ?_, rfl⟩
  refine Subgroup.mem_centralizer_iff.mpr fun e he => ?_
  exact (Subgroup.mem_centralizer_iff.mp
    (mem_elemThompsonCenterTorsion_iff_centralizer.mp he).1 j hj).symm

end BaumannIn

section Sup

variable {G : Type*} [Group G] [Finite G]

theorem mem_normalizer_sup' {A B : Subgroup G} {y : G}
    (hA : y ∈ Subgroup.normalizer (A : Set G)) (hB : y ∈ Subgroup.normalizer (B : Set G)) :
    y ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  apply mem_normalizer_of_le_cj
  rw [cj_sup]
  exact sup_le_sup (fun x hx => mem_cj.mpr ((Subgroup.mem_normalizer_iff.mp hA x).mp hx))
    (fun x hx => mem_cj.mpr ((Subgroup.mem_normalizer_iff.mp hB x).mp hx))

end Sup

section Main

variable {G : Type*} [Group G] [Finite G]

open scoped commutatorElement in
theorem Baumann_central_splitting_and_Sylow_transfer
    (p : ℕ) [Fact p.Prime] (V : Subgroup G) [V.Normal] (hV : IsElementaryAbelian p V)
    (R : Subgroup G) (hR : IsPGroup p R) (hVR : V ≤ R)
    (L : Subgroup G) (hL : L = Subgroup.closure {g : G | Nat.Coprime (orderOf g) p})
    (hLR : L ⊔ R = ⊤) (Q P : Subgroup G) (hQ : Q = R ⊓ Subgroup.centralizer (V : Set G))
    (hP : P = inSubgroup (pCore p) L) (hPQ : P ≤ Q)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hΦ : ((Subgroup.centralizer (V : Set G)).subgroupOf L).map
        (QuotientGroup.mk' (CFSG.pCore p L)) ≤ frattini (L ⧸ CFSG.pCore p L))
    (hineq : ∀ A ∈ elemThompsonFamily R p,
      (A ⊓ Subgroup.centralizer ((V.subgroupOf R : Subgroup R) : Set R)).relIndex A ≤
        ((V.subgroupOf R) ⊓ Subgroup.centralizer (A : Set R)).relIndex (V.subgroupOf R))
    (n : ℕ) (hn : 1 ≤ n) (X : Fin n → Subgroup G)
    (hXL : ∀ i, ∃ l ∈ L, conjugate (X i) l ≤ R)
    (hXJ : ∀ i, (elemThompson (X i) p).map (X i).subtype = X i)
    (hXe : ∀ i, pRank p (X i) = pRank p R)
    (I : Subgroup G) (hI : I = ⨆ i, X i)
    (hρ : L.map (MulAut.conjNormal (H := V)) ≤ I.map (MulAut.conjNormal (H := V)))
    (J : Subgroup G) (hJ : J = (elemThompson R p).map R.subtype) (hJI : J ≤ I)
    (hcodim : ∏ i, (V ⊓ Subgroup.centralizer (X i : Set G)).relIndex V ≤
      (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V)
    (S E : Subgroup G) (hS : S = elemBaumannIn p R) (hE : E = elemCenterIn p R) :
    P ≤ S ∧
      E = (E ⊓ Subgroup.centralizer (L : Set G)) ⊔ (V ⊓ Subgroup.centralizer (J : Set G)) ∧
      (IsSylowIn p Q (Subgroup.centralizer (V : Set G)) →
        IsSylowIn p (S ⊓ Subgroup.centralizer (V : Set G))
          ((L ⊔ S) ⊓ Subgroup.centralizer (V : Set G)) ∧
        (IsSylowIn p (S.map (MulAut.conjNormal (H := V)))
            ((L ⊔ S).map (MulAut.conjNormal (H := V))) → IsSylowIn p S (L ⊔ S))) := by
  classical
  obtain ⟨hQn, ⟨hIcl, hIn⟩, hLI, -⟩ :=
    qt_nq_frattini_thompson_normal_closure_generation p V hV R hR hVR L hL hLR Q P hQ hP hPQ hLQ
      hΦ n hn X hXL hXJ hXe I hI hρ J hJ hJI
  have : Q.Normal := hQn
  have : I.Normal := hIn
  have hL' : L = BlueprintB2.pPrimeGen p (⊤ : Subgroup G) := by
    rw [hL, BlueprintB2.pPrimeGen]
    congr 1
    ext x
    simp
  have hLn : L.Normal := hL' ▸ BlueprintB2.pPrimeGen_top_normal
  have hJdef : J = elemThompsonIn p R := hJ
  have hJR : J ≤ R := hJdef ▸ elemThompsonIn_le p R
  have hER : E ≤ R := hE ▸ elemCenterIn_le_self
  have hSR : S ≤ R := hS ▸ elemBaumannIn_le p R
  have hIR : I ⊔ R = ⊤ := top_unique (hLR ▸ sup_le_sup_right hLI R)
  have hV'e : IsElementaryAbelian p (V.subgroupOf R) := isElementaryAbelian_subgroupOf hV
  obtain ⟨-, -, -, hEQ, hVQ, -, hcomm⟩ := equal_rank_elementary_centralizer_replacement hR
    (V.subgroupOf R) hV'e (Subgroup.centralizer ((V.subgroupOf R : Subgroup R) : Set R)) rfl hineq
  set Q' : Subgroup R := Subgroup.centralizer ((V.subgroupOf R : Subgroup R) : Set R) with hQ'
  have hQ'map : Q'.map R.subtype = Q := by
    rw [hQ]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      have := Subgroup.mem_centralizer_iff.mp hy ⟨v, hVR hv⟩ (Subgroup.mem_subgroupOf.mpr hv)
      exact congrArg Subtype.val this
    · rintro ⟨hxR, hxc⟩
      refine ⟨⟨x, hxR⟩, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_, rfl⟩
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc (v : G) hv)
  have hEQeq : (elemCenterIn p Q').map R.subtype = elemCenterIn p Q := by
    rw [elemCenterIn_map_subtype, hQ'map]
  have hEQn : (elemCenterIn p Q).Normal := elemCenterIn_normal p Q
  have hEQe : IsElementaryAbelian p (elemCenterIn p Q) := elemCenterIn_isElementaryAbelian p Q
  have hER' : E ≤ elemCenterIn p Q := by
    rw [← hEQeq, hE]
    exact Subgroup.map_mono hEQ
  have hVEQ : V ≤ elemCenterIn p Q := by
    rw [← hEQeq]
    calc V = (V.subgroupOf R).map R.subtype := (Subgroup.map_subgroupOf_eq_of_le hVR).symm
      _ ≤ _ := Subgroup.map_mono hVQ
  have hcommEQ : ⁅elemCenterIn p Q, J⁆ ≤ V := by
    rw [← hEQeq, hJ, ← Subgroup.map_commutator]
    calc (⁅elemCenterIn p Q', elemThompson R p⁆).map R.subtype ≤ (V.subgroupOf R).map R.subtype :=
          Subgroup.map_mono hcomm
      _ = V := Subgroup.map_subgroupOf_eq_of_le hVR
  have hEI : ∀ e ∈ elemCenterIn p Q, ∀ x ∈ I, ⁅e, x⁆ ∈ V := by
    have key := commutator_normalClosure_mem (Q := elemCenterIn p Q) (E := V) (A := J) (by
      intro g q hq a ha
      have haJ : g * a * g⁻¹ ∈ J := mem_cj.mp ha
      have hqg : g * q * g⁻¹ ∈ elemCenterIn p Q := hEQn.conj_mem q hq g
      have h1 : ⁅g * q * g⁻¹, g * a * g⁻¹⁆ ∈ V :=
        hcommEQ (Subgroup.commutator_mem_commutator hqg haJ)
      have h2 : ⁅q, a⁆ = g⁻¹ * ⁅g * q * g⁻¹, g * a * g⁻¹⁆ * g⁻¹⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [h2]
      exact (inferInstance : V.Normal).conj_mem _ h1 g⁻¹)
    intro e he x hx
    exact key e he x (hIcl ▸ hx)
  set Wg : Subgroup G := E ⊔ V with hWg
  have hWEQ : Wg ≤ elemCenterIn p Q := sup_le hER' hVEQ
  have hWe : IsElementaryAbelian p Wg := isElementaryAbelian_of_le hWEQ hEQe
  have hWR : Wg ≤ R := sup_le hER hVR
  have hcommW : ∀ a ∈ Wg, ∀ b ∈ Wg, a * b = b * a := (isElementaryAbelian_iff.mp hWe).1
  have hVW : V ≤ Wg := le_sup_right
  have hEW : E ≤ Wg := le_sup_left
  have hIW : ∀ x ∈ I, x ∈ Subgroup.normalizer (Wg : Set G) := by
    intro x hx
    rw [hWg, sup_comm]
    refine mem_normalizer_sup_of_commutator (mem_normalizer_of_normal V x) (fun w hw => ?_)
    have h1 := hEI w (hER' hw) x hx
    have : x * w * x⁻¹ * w⁻¹ = ⁅w, x⁆⁻¹ := by simp only [commutatorElement_def]; group
    rw [this]
    exact inv_mem h1
  have hRW : ∀ r ∈ R, r ∈ Subgroup.normalizer (Wg : Set G) := by
    intro r hr
    have hEn : r ∈ Subgroup.normalizer (E : Set G) := by
      rw [hE]; exact le_normalizer_elemCenterIn p R hr
    exact mem_normalizer_sup' hEn (mem_normalizer_of_normal V r)
  have hWn : Wg.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    rw [eq_top_iff, ← hIR]
    exact sup_le (fun x hx => hIW x hx) (fun r hr => hRW r hr)
  have hEJ : ∀ e ∈ E, ∀ j ∈ J, j * e = e * j := by
    intro e he j hj
    exact (mem_elemCenterIn_iff_centralizer.mp (hE ▸ he)).2.2 j (hJdef ▸ hj)
  have hEC : E ≤ Subgroup.centralizer (J : Set G) := fun e he =>
    Subgroup.mem_centralizer_iff.mpr fun j hj => hEJ e he j hj
  have hWJ : Wg = (Wg ⊓ Subgroup.centralizer (J : Set G)) ⊔ V :=
    le_antisymm (sup_le (le_sup_of_le_left (le_inf hEW hEC)) le_sup_right)
      (sup_le inf_le_left hVW)
  have hWX : ∀ i, Wg = (Wg ⊓ Subgroup.centralizer (X i : Set G)) ⊔ V := by
    intro i
    obtain ⟨l, -, hlR⟩ := hXL i
    have hXi : X i ≤ cj J l⁻¹ := by
      have := le_conjugate_inv_of_conjugate_le (hXJ i) (hXe i) hlR
      rw [hJ]; exact this
    have h1 := congrArg (fun K => cj K l⁻¹) hWJ
    simp only [cj_sup, cj_inf] at h1
    rw [cj_eq_self_of_normal (Y := Wg), cj_eq_self_of_normal (Y := V), ← centralizer_cj] at h1
    refine le_antisymm ?_ (sup_le inf_le_left hVW)
    calc Wg = (Wg ⊓ Subgroup.centralizer ((cj J l⁻¹ : Subgroup G) : Set G)) ⊔ V := h1
      _ ≤ (Wg ⊓ Subgroup.centralizer (X i : Set G)) ⊔ V :=
        sup_le_sup_right (inf_le_inf_left _ (Subgroup.centralizer_le hXi)) V
  have hLX : L ≤ ⨆ i, X i := hI ▸ hLI
  obtain ⟨-, hVLidx⟩ := saturation_index V X L hLX hcodim
  have hidxW : ∀ i, (V ⊓ Subgroup.centralizer (X i : Set G)).relIndex V =
      (Wg ⊓ Subgroup.centralizer (X i : Set G)).relIndex Wg := by
    intro i
    have h := relIndex_inf_eq_relIndex_of_sup (W := Wg) (V := V)
      (A := Wg ⊓ Subgroup.centralizer (X i : Set G)) inf_le_left (hWX i).symm
      (fun a ha v hv => hcommW a ha.1 v (hVW hv))
    have hAV : (Wg ⊓ Subgroup.centralizer (X i : Set G)) ⊓ V =
        V ⊓ Subgroup.centralizer (X i : Set G) := by
      ext x
      constructor
      · rintro ⟨⟨hxW, hxc⟩, hxV⟩
        exact ⟨hxV, hxc⟩
      · rintro ⟨hxV, hxc⟩
        exact ⟨⟨hVW hxV, hxc⟩, hxV⟩
    rw [hAV] at h
    exact h
  have hgeW : ∏ i, (Wg ⊓ Subgroup.centralizer (X i : Set G)).relIndex Wg ≤
      (Wg ⊓ Subgroup.centralizer (L : Set G)).relIndex Wg := by
    calc ∏ i, (Wg ⊓ Subgroup.centralizer (X i : Set G)).relIndex Wg
        = ∏ i, (V ⊓ Subgroup.centralizer (X i : Set G)).relIndex V :=
          Finset.prod_congr rfl fun i _ => (hidxW i).symm
      _ = (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V := hVLidx.symm
      _ ≤ (Wg ⊓ Subgroup.centralizer (L : Set G)).relIndex Wg := relIndex_inf_le_of_le hVW _
  obtain ⟨hWL, hWLidx⟩ := saturation_index Wg X L hLX hgeW
  set U : Subgroup G := Wg ⊓ Subgroup.centralizer (L : Set G) with hU
  have hUV : U ⊓ V = V ⊓ Subgroup.centralizer (L : Set G) := by
    ext x
    constructor
    · rintro ⟨⟨hxW, hxc⟩, hxV⟩
      exact ⟨hxV, hxc⟩
    · rintro ⟨hxV, hxc⟩
      exact ⟨⟨hVW hxV, hxc⟩, hxV⟩
  have hidxU : (U ⊓ V).relIndex V = U.relIndex Wg := by
    rw [hUV, hVLidx]
    show _ = (Wg ⊓ Subgroup.centralizer (L : Set G)).relIndex Wg
    rw [hWLidx]
    exact Finset.prod_congr rfl fun i _ => hidxW i
  have hWUV : U ⊔ V = Wg := by
    have hUc : ∀ a ∈ U, ∀ v ∈ V, a * v = v * a := fun a ha v hv => hcommW a ha.1 v (hVW hv)
    have hprod := card_sup_mul_card_inf hUc
    have h1 : (U ⊓ V).relIndex V * Nat.card (U ⊓ V : Subgroup G) = Nat.card V := by
      have := Subgroup.relIndex_mul_card (U ⊓ V) V
      rwa [inf_of_le_left (inf_le_right : U ⊓ V ≤ V)] at this
    have h2 : U.relIndex Wg * Nat.card U = Nat.card Wg := by
      have := Subgroup.relIndex_mul_card U Wg
      rwa [inf_of_le_left (inf_le_left : U ≤ Wg)] at this
    have hpos : 0 < Nat.card (U ⊓ V : Subgroup G) := Nat.card_pos
    have key : Nat.card (U ⊔ V : Subgroup G) * Nat.card (U ⊓ V : Subgroup G) =
        Nat.card Wg * Nat.card (U ⊓ V : Subgroup G) := by
      calc Nat.card (U ⊔ V : Subgroup G) * Nat.card (U ⊓ V : Subgroup G)
          = Nat.card U * Nat.card V := hprod
        _ = Nat.card U * ((U ⊓ V).relIndex V * Nat.card (U ⊓ V : Subgroup G)) := by rw [h1]
        _ = (U.relIndex Wg * Nat.card U) * Nat.card (U ⊓ V : Subgroup G) := by rw [hidxU]; ring
        _ = Nat.card Wg * Nat.card (U ⊓ V : Subgroup G) := by rw [h2]
    have hcard := Nat.eq_of_mul_eq_mul_right hpos key
    exact Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left hVW) hcard.ge
  have hUE : U ≤ E := by
    intro u hu
    have huR : u ∈ R := hWR hu.1
    have hup : u ^ p = 1 := (isElementaryAbelian_iff.mp hWe).2 u hu.1
    have hu' : u ∈ Wg ⊓ Subgroup.centralizer ((⨆ i, X i : Subgroup G) : Set G) := by
      rw [← hWL]; exact hu
    rw [← hI] at hu'
    have huJ : u ∈ Subgroup.centralizer (J : Set G) := Subgroup.centralizer_le hJI hu'.2
    rw [hE]
    exact mem_elemCenterIn_iff_centralizer.mpr ⟨huR, hup, fun j hj =>
      Subgroup.mem_centralizer_iff.mp huJ j (hJdef ▸ hj)⟩
  have hUeq : U = E ⊓ Subgroup.centralizer (L : Set G) :=
    le_antisymm (le_inf hUE inf_le_right) (inf_le_inf_right _ hEW)
  have hEV : E ⊓ V = V ⊓ Subgroup.centralizer (J : Set G) := by
    ext v
    constructor
    · rintro ⟨hvE, hvV⟩
      exact ⟨hvV, Subgroup.mem_centralizer_iff.mpr fun j hj => hEJ v hvE j hj⟩
    · rintro ⟨hvV, hvJ⟩
      refine ⟨?_, hvV⟩
      rw [hE]
      exact mem_elemCenterIn_iff_centralizer.mpr ⟨hVR hvV,
        (isElementaryAbelian_iff.mp hV).2 v hvV,
        fun j hj => Subgroup.mem_centralizer_iff.mp hvJ j (hJdef ▸ hj)⟩
  have hE2 : E = (E ⊓ Subgroup.centralizer (L : Set G)) ⊔ (V ⊓ Subgroup.centralizer (J : Set G)) := by
    apply le_antisymm
    · intro e he
      have heW : e ∈ U ⊔ V := hWUV ▸ hEW he
      obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp heW
      have hvE : v ∈ E := by
        have := mul_mem (inv_mem (hUE hu)) he
        simpa using this
      exact mul_mem (Subgroup.mem_sup_left (hUeq ▸ hu)) (Subgroup.mem_sup_right (hEV ▸ ⟨hvE, hv⟩))
    · exact sup_le inf_le_left (hEV ▸ inf_le_left)
  have hcentE : ∀ x : G, (∀ e ∈ E ⊓ Subgroup.centralizer (L : Set G), x * e = e * x) →
      (∀ e ∈ V ⊓ Subgroup.centralizer (J : Set G), x * e = e * x) → ∀ e ∈ E, x * e = e * x := by
    intro x h1 h2 e he
    have hle : (E ⊓ Subgroup.centralizer (L : Set G)) ⊔ (V ⊓ Subgroup.centralizer (J : Set G)) ≤
        Subgroup.centralizer ({x} : Set G) := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact h1 y hy
      · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact h2 y hy
    exact Subgroup.mem_centralizer_iff.mp (hle (hE2 ▸ he)) x (Set.mem_singleton x)
  have hPL : P ≤ L := by
    rw [hP]
    unfold inSubgroup
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hQR : Q ≤ R := hQ ▸ inf_le_left
  have hQC : Q ≤ Subgroup.centralizer (V : Set G) := hQ ▸ inf_le_right
  have hPS : P ≤ S := by
    intro x hx
    have hxL : x ∈ L := hPL hx
    have hxQ : x ∈ Q := hPQ hx
    rw [hS, mem_elemBaumannIn_iff]
    refine ⟨hQR hxQ, fun e he => ?_⟩
    have := hcentE x (fun y hy => Subgroup.mem_centralizer_iff.mp hy.2 x hxL)
      (fun y hy => (Subgroup.mem_centralizer_iff.mp (hQC hxQ) y hy.1).symm) e (hE ▸ he)
    exact this.symm
  refine ⟨hPS, hE2, fun hQsyl => ?_⟩
  have hRS : ∀ r ∈ R, r ∈ Subgroup.normalizer (S : Set G) := by
    have key : ∀ r ∈ R, ∀ s ∈ S, r * s * r⁻¹ ∈ S := by
      intro r hr s hs
      rw [hS, mem_elemBaumannIn_iff] at hs ⊢
      refine ⟨mul_mem (mul_mem hr hs.1) (inv_mem hr), fun e he => ?_⟩
      have he' : r⁻¹ * e * r ∈ elemCenterIn p R := by
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_elemCenterIn p R (R.inv_mem hr)) e).mp he
        simpa using this
      have h1 := hs.2 (r⁻¹ * e * r) he'
      calc e * (r * s * r⁻¹) = r * ((r⁻¹ * e * r) * s) * r⁻¹ := by group
        _ = r * (s * (r⁻¹ * e * r)) * r⁻¹ := by rw [h1]
        _ = (r * s * r⁻¹) * e := by group
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨key r hr x, fun hx => by simpa [mul_assoc] using key r⁻¹ (R.inv_mem hr) _ hx⟩
  have hLSn : (L ⊔ S).Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    rw [eq_top_iff, ← hLR]
    exact sup_le (fun l hl => Subgroup.le_normalizer (Subgroup.mem_sup_left hl))
      (fun r hr => mem_normalizer_sup' (mem_normalizer_of_normal L r) (hRS r hr))
  have h3a : IsSylowIn p (S ⊓ Subgroup.centralizer (V : Set G))
      ((L ⊔ S) ⊓ Subgroup.centralizer (V : Set G)) := by
    have hN : ((((L ⊔ S) ⊓ Subgroup.centralizer (V : Set G)) :
        Subgroup G).subgroupOf (Subgroup.centralizer (V : Set G))).Normal := by
      rw [Subgroup.inf_subgroupOf_right]
      infer_instance
    have h := hQsyl.inf_normal (N := (L ⊔ S) ⊓ Subgroup.centralizer (V : Set G)) inf_le_right hN
    have hQS : Q ⊓ ((L ⊔ S) ⊓ Subgroup.centralizer (V : Set G)) =
        S ⊓ Subgroup.centralizer (V : Set G) := by
      apply le_antisymm
      · rintro x ⟨hxQ, hxLS, hxC⟩
        obtain ⟨l, hl, s, hs, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxLS
        have hxS : l * s ∈ S := by
          rw [hS, mem_elemBaumannIn_iff]
          refine ⟨hQR hxQ, fun e he => ?_⟩
          have hsS : s ∈ elemBaumannIn p R := hS ▸ hs
          have hs2 := (mem_elemBaumannIn_iff.mp hsS).2
          have := hcentE (l * s) (fun y hy => by
            have hyL : l * y = y * l := Subgroup.mem_centralizer_iff.mp hy.2 l hl
            have hys : y * s = s * y := hs2 y (hE ▸ hy.1)
            calc l * s * y = l * (s * y) := by group
              _ = l * (y * s) := by rw [hys]
              _ = (l * y) * s := by group
              _ = (y * l) * s := by rw [hyL]
              _ = y * (l * s) := by group)
            (fun y hy => (Subgroup.mem_centralizer_iff.mp hxC y hy.1).symm) e (hE ▸ he)
          exact this.symm
        exact ⟨hxS, hxC⟩
      · rintro x ⟨hxS, hxC⟩
        exact ⟨by rw [hQ]; exact ⟨hSR hxS, hxC⟩, Subgroup.mem_sup_right hxS, hxC⟩
    rwa [hQS] at h
  refine ⟨h3a, fun hρS => ?_⟩
  have hfinM : Finite (MulAut V) :=
    Finite.of_injective (fun f : MulAut V => (f : V → V)) (fun f g h => MulEquiv.ext (congrFun h))
  set f : G →* MulAut V := MulAut.conjNormal (H := V) with hf
  have hker : f.ker = Subgroup.centralizer (V : Set G) := by
    ext g
    constructor
    · intro hg
      exact mem_centralizer_of_conjNormal_eq_one hg
    · intro hg
      rw [MonoidHom.mem_ker]
      refine MulEquiv.ext fun v => Subtype.ext ?_
      have h1 : (v : G) * g = g * (v : G) := Subgroup.mem_centralizer_iff.mp hg (v : G) v.2
      show g * (v : G) * g⁻¹ = (v : G)
      rw [← h1]; group
  have c1 := card_eq_card_map_mul_card_inf_ker f (L ⊔ S)
  have c2 := card_eq_card_map_mul_card_inf_ker f S
  rw [hker] at c1 c2
  have s1 := h3a.card_eq
  have s2 := hρS.card_eq
  have hpos1 : Nat.card ((L ⊔ S).map f) ≠ 0 := Nat.card_pos.ne'
  have hpos2 : Nat.card (((L ⊔ S) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G)) ≠ 0 :=
    Nat.card_pos.ne'
  refine isSylowIn_of_card_eq le_sup_right ?_
  rw [c2, s1, s2, c1, Nat.factorization_mul hpos1 hpos2, Finsupp.add_apply, pow_add]

end Main


end CFSG.QuasithinUnique.Setup.Campbell
