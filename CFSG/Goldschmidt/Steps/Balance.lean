module

public import CFSG.Goldschmidt.StatementsH
import CFSG.Goldschmidt.Steps.Ind
import CFSG.Goldschmidt.Steps.IHConseq
import CFSG.Goldschmidt.Steps.AxB
import CFSG.Goldschmidt.Steps.Components
import CFSG.Goldschmidt.Steps.TICrit
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore

public section

namespace CFSG.Goldschmidt

open CFSG.Open

namespace Balance

section General

variable {Y : Type*} [Group Y]

theorem mem_normalizer_of_conj_mem {K : Subgroup Y} {g : Y} (h₁ : ∀ y ∈ K, g * y * g⁻¹ ∈ K)
    (h₂ : ∀ y ∈ K, g⁻¹ * y * g ∈ K) : g ∈ Subgroup.normalizer (K : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h₁ y, fun hy => ?_⟩
  have := h₂ _ hy
  rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at this

theorem conj_mem_oddCoreOf {H : Subgroup Y} {h y : Y} (hh : h ∈ H) (hy : y ∈ oddCoreOf H) :
    h * y * h⁻¹ ∈ oddCoreOf H := by
  obtain ⟨o, ho, rfl⟩ := hy
  exact ⟨⟨h, hh⟩ * o * ⟨h, hh⟩⁻¹, (goldschmidtOddCore_normal H).conj_mem o ho ⟨h, hh⟩, rfl⟩

theorem odd_card_oddCoreOf [Finite Y] (H : Subgroup Y) : Odd (Nat.card (oddCoreOf H)) := by
  rw [oddCoreOf, Subgroup.card_map_of_injective H.subtype_injective]
  exact CFSG.ComponentClassification.OddCore.odd_card H

theorem oddCoreOf_le_of_normal [Finite Y] {M X : Subgroup Y} (hMX : M ≤ X)
    (hMn : (M.subgroupOf X).Normal) : oddCoreOf M ≤ oddCoreOf X := by
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨hX, hO⟩ := (CFSG.ComponentClassification.OddCore.subnormal_mem_iff
    (IsSubnormal.step hMX hMn (IsSubnormal.refl X)) m.1 m.2).mp hm
  exact ⟨⟨m.1, hX⟩, hO, rfl⟩

theorem eq_bot_of_odd_of_le_normal [Finite Y] (hO : goldschmidtOddCore Y = ⊥)
    {F R : Subgroup Y} (hF : F.Normal) (hRF : R ≤ F)
    (hFR : F ≤ Subgroup.normalizer (R : Set Y)) (hR : Odd (Nat.card R)) : R = ⊥ := by
  have hFO : componentClassificationOddCore F = ⊥ :=
    CFSG.ComponentClassification.OddCore.subnormal_corefree hO F
      (CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hF.isSubnormal)
  have hN : (R.subgroupOf F).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRF).mpr hFR
  have hodd : Odd (Nat.card (R.subgroupOf F)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRF).toEquiv]
    exact hR
  have hle := CFSG.ComponentClassification.OddCore.maximal F _ hN hodd
  rw [hFO, le_bot_iff, Subgroup.subgroupOf_eq_bot] at hle
  exact hle.eq_bot_of_le hRF

end General

variable {G : Type} [Group G] [Finite G]

theorem le_oddCoreOf {X V D : Subgroup G} (hVX : V ≤ X) (hVab : IsMulCommutative V)
    (hVn : ((V.subgroupOf X).map (QuotientGroup.mk' (goldschmidtOddCore X))).Normal)
    {v : G} (hv : v ∈ V) (hv2 : v ^ 2 = 1) (hDX : D ≤ X) (hD : Odd (Nat.card D))
    (hDv : D ≤ Subgroup.centralizer ({v} : Set G))
    (hCD : X ⊓ Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (D : Set G)) :
    D ≤ oddCoreOf X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := goldschmidtOddCore X with hNdef
  set π := QuotientGroup.mk' N with hπdef
  set x : X := ⟨v, hVX hv⟩ with hxdef
  set Db : Subgroup (X ⧸ N) := (D.subgroupOf X).map π with hDbdef
  set P := CFSG.Open.pCore 2 (X ⧸ N) with hPdef
  set E := goldschmidtLayer (X ⧸ N) with hEdef
  set B := Subgroup.zpowers (π x) with hBdef
  have hO : goldschmidtOddCore (X ⧸ N) = ⊥ := goldschmidtOddCore_quotient_eq_bot X
  have hPn : P.Normal := CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal 2
  have hPp : IsPGroup 2 P := CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup 2
  have hEn : E.Normal := CFSG.ComponentClassification.Layer.normal _
  have hDb : Odd (Nat.card Db) := by
    refine hD.of_dvd_nat ((Subgroup.card_map_dvd _ _).trans ?_)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDX).toEquiv]
  have hxp : IsPGroup 2 (Subgroup.zpowers x) := by
    have hx2 : x ^ 2 = 1 := Subtype.ext (by simpa [hxdef] using hv2)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show orderOf x ∣ 2 ^ 1 by rw [pow_one]; exact orderOf_dvd_of_pow_eq_one hx2)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  have hB : IsPGroup 2 B := by
    rw [hBdef, ← MonoidHom.map_zpowers]
    exact hxp.map π
  have hcent : Subgroup.centralizer (B : Set (X ⧸ N)) ≤ Subgroup.normalizer (Db : Set (X ⧸ N)) := by
    have : Fact (IsPGroup 2 (Subgroup.zpowers x)) := ⟨hxp⟩
    have h : Subgroup.centralizer (((Subgroup.zpowers x).map π : Subgroup (X ⧸ N)) :
        Set (X ⧸ N)) = (Subgroup.centralizer ((Subgroup.zpowers x : Subgroup X) : Set X)).map π :=
      CFSG.centralizer_map_quotient_eq_map_centralizer 2 (Subgroup.zpowers x) N
        inferInstance (Nat.coprime_two_left.mpr (CFSG.ComponentClassification.OddCore.odd_card X))
    rw [MonoidHom.map_zpowers] at h
    rw [hBdef, h]
    rintro _ ⟨c, hc, rfl⟩
    have hcx : x * c = c * x := Subgroup.mem_centralizer_iff.mp hc x (Subgroup.mem_zpowers x)
    have hcv : (c : G) ∈ X ⊓ Subgroup.centralizer ({v} : Set G) :=
      ⟨c.2, Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hcx).symm⟩
    have hcN : c ∈ Subgroup.normalizer ((D.subgroupOf X : Subgroup X) : Set X) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hDX]
      exact hCD hcv
    exact Subgroup.le_normalizer_map π ⟨c, hcN, rfl⟩
  have hDbB : ⁅Db, B⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff, hBdef,
      Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    have hdv : (d : G) * v = v * d := Subgroup.mem_centralizer_singleton_iff.mp (hDv hd)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hdv
  have hDbP : Disjoint Db P := by
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    exact Subgroup.disjoint_of_coprime_natCard
      (hn ▸ (Nat.coprime_two_right.mpr hDb).pow_right n)
  have hPC : P ⊓ Subgroup.centralizer (B : Set (X ⧸ N)) ≤
      Subgroup.centralizer (Db : Set (X ⧸ N)) := by
    rintro y ⟨hyP, hyC⟩
    have hyN := hcent hyC
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have h1 : d * y * d⁻¹ * y⁻¹ ∈ Db := by
      have : y * d⁻¹ * y⁻¹ ∈ Db := (Subgroup.mem_normalizer_iff.mp hyN _).mp (Db.inv_mem hd)
      have h := Db.mul_mem hd this
      rwa [show d * (y * d⁻¹ * y⁻¹) = d * y * d⁻¹ * y⁻¹ by group] at h
    have h2 : d * y * d⁻¹ * y⁻¹ ∈ P := P.mul_mem (hPn.conj_mem y hyP d) (P.inv_mem hyP)
    have h3 := Subgroup.disjoint_def.mp hDbP h1 h2
    calc d * y = d * y * d⁻¹ * y⁻¹ * (y * d) := by group
      _ = y * d := by rw [h3, one_mul]
  have hPDb : P ≤ Subgroup.centralizer (Db : Set (X ⧸ N)) :=
    N10 (X ⧸ N) P Db B hPp (Nat.coprime_two_right.mpr hDb) hB
      (le_top.trans (Subgroup.normalizer_eq_top_iff.mpr hPn).ge)
      (le_top.trans (Subgroup.normalizer_eq_top_iff.mpr hPn).ge) hDbB hPC
  have hEB : E ≤ Subgroup.centralizer (B : Set (X ⧸ N)) := by
    set Vb := (V.subgroupOf X).map π with hVbdef
    have : IsMulCommutative Vb := isMulCommutative_map (isMulCommutative_subgroupOf hVab X) π
    have hsolv : Group.IsSolvable Vb := inferInstance
    have hxV : π x ∈ Vb := ⟨x, hv, rfl⟩
    refine le_trans (b := Subgroup.centralizer (Vb : Set (X ⧸ N))) (sSup_le fun K hK => ?_)
      (Subgroup.centralizer_le fun y hy => Subgroup.zpowers_le.mpr hxV hy)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (N8c (X ⧸ N) K Vb hK hVn hsolv)
  have hENDb : E ≤ Subgroup.normalizer (Db : Set (X ⧸ N)) := hEB.trans hcent
  have hDbE : Db ⊓ E = ⊥ := by
    refine eq_bot_of_odd_of_le_normal hO hEn inf_le_right (fun e he => ?_)
      (hDb.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
    refine mem_normalizer_of_conj_mem (fun y hy => ⟨?_, ?_⟩) (fun y hy => ⟨?_, ?_⟩)
    · exact (Subgroup.mem_normalizer_iff.mp (hENDb he) y).mp hy.1
    · exact hEn.conj_mem y hy.2 e
    · have := (Subgroup.mem_normalizer_iff.mp (hENDb (E.inv_mem he)) y).mp hy.1
      rwa [inv_inv] at this
    · have := hEn.conj_mem y hy.2 e⁻¹
      rwa [inv_inv] at this
  have hEDb : E ≤ Subgroup.centralizer (Db : Set (X ⧸ N)) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have h1 : d * e * d⁻¹ * e⁻¹ ∈ Db := by
      have : e * d⁻¹ * e⁻¹ ∈ Db :=
        (Subgroup.mem_normalizer_iff.mp (hENDb he) _).mp (Db.inv_mem hd)
      have h := Db.mul_mem hd this
      rwa [show d * (e * d⁻¹ * e⁻¹) = d * e * d⁻¹ * e⁻¹ by group] at h
    have h2 : d * e * d⁻¹ * e⁻¹ ∈ E := E.mul_mem (hEn.conj_mem e he d) (E.inv_mem he)
    have h3 : d * e * d⁻¹ * e⁻¹ = 1 := by
      have h : d * e * d⁻¹ * e⁻¹ ∈ Db ⊓ E := ⟨h1, h2⟩
      rw [hDbE] at h
      exact Subgroup.mem_bot.mp h
    calc d * e = d * e * d⁻¹ * e⁻¹ * (e * d) := by group
      _ = e * d := by rw [h3, one_mul]
  have hFDb : P ⊔ E ≤ Subgroup.centralizer (Db : Set (X ⧸ N)) := sup_le hPDb hEDb
  have hDbF : Db ≤ P ⊔ E :=
    (Subgroup.le_centralizer_iff.mp hFDb).trans ((N8d (X ⧸ N) hO).2.2)
  have hDb0 : Db = ⊥ := eq_bot_of_odd_of_le_normal hO (Subgroup.sup_normal P E) hDbF
    (hFDb.trans (Subgroup.centralizer_le_normalizer _)) hDb
  have hDN : D.subgroupOf X ≤ N := by
    have h := (Subgroup.map_eq_bot_iff _).mp hDb0
    rwa [QuotientGroup.ker_mk'] at h
  intro d hd
  exact ⟨⟨d, hDX hd⟩, hDN hd, rfl⟩

end Balance

open Balance in
theorem N36 : S_N36 := by
  intro G _ _ _ hnab hIH S U hUS hUel hcl hK1
  have hU2 : IsPGroup 2 U := S.isPGroup'.to_le hUS
  have hUC : ∀ w ∈ U, U ≤ Subgroup.centralizer ({w} : Set G) := fun w hw v hv =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hUel.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩))
  have key : ∀ w ∈ U, w ≠ 1 →
      Subgroup.centralizer ({w} : Set G) = oddCoreOf (Subgroup.centralizer ({w} : Set G)) ⊔
        (Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.normalizer (U : Set G)) ∧
      ((U.subgroupOf (Subgroup.centralizer ({w} : Set G))).map
        (QuotientGroup.mk' (goldschmidtOddCore (Subgroup.centralizer ({w} : Set G))))).Normal := by
    intro w hw hw1
    set X := Subgroup.centralizer ({w} : Set G) with hXdef
    set M := normalClosureIn X U with hMdef
    set π := QuotientGroup.mk' (goldschmidtOddCore X) with hπdef
    have hUX : U ≤ X := hUC w hw
    obtain ⟨T, hUT, hTX⟩ := TICrit.exists_fusionIsSylowIn hU2 hUX
    obtain ⟨-, hC1, -, -, hC4⟩ := N16_of N1 (Nat.card G) hIH G S U X T hUS hUel.1 hcl hUT hTX
      (TICrit.card_centralizer_lt hnab hw1)
    have hM : M = oddCoreOf M ⊔ U := (hC4 (hK1 w hw hw1)).1
    have hMX : M ≤ X := Subgroup.map_subtype_le _
    have hMn : (M.subgroupOf X).Normal := by
      have hMsub : M.subgroupOf X =
          Subgroup.normalClosure ((U.subgroupOf X : Subgroup X) : Set X) :=
        Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
      rw [hMsub]
      exact Subgroup.normalClosure_normal
    have hUM : U ≤ M := fun a ha =>
      ⟨⟨a, hUX ha⟩, Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.2 ha), rfl⟩
    have hOM : oddCoreOf M ≤ oddCoreOf X := oddCoreOf_le_of_normal hMX hMn
    refine ⟨le_antisymm ?_ (sup_le (Subgroup.map_subtype_le _) inf_le_left), ?_⟩
    · refine hC1.ge.trans (sup_le ?_ le_sup_right)
      exact hM.le.trans (sup_le (hOM.trans le_sup_left)
        (le_sup_of_le_right (le_inf hUX Subgroup.le_normalizer)))
    · have heq : (U.subgroupOf X).map π = (M.subgroupOf X).map π := by
        refine le_antisymm (Subgroup.map_mono fun y hy => hUM hy) ?_
        have h1 : M.subgroupOf X ≤ U.subgroupOf X ⊔ goldschmidtOddCore X := by
          intro y hy
          have hyM : (y : G) ∈ oddCoreOf M ⊔ U := hM ▸ hy
          have h2 : oddCoreOf M ⊔ U ≤ (U.subgroupOf X ⊔ goldschmidtOddCore X).map X.subtype := by
            rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_of_le_left hUX]
            exact sup_le (hOM.trans le_sup_right) le_sup_left
          exact (Subgroup.mem_map_iff_mem X.subtype_injective).mp (h2 hyM)
        calc (M.subgroupOf X).map π ≤ (U.subgroupOf X ⊔ goldschmidtOddCore X).map π :=
              Subgroup.map_mono h1
          _ = (U.subgroupOf X).map π := by
              rw [Subgroup.map_sup, hπdef, QuotientGroup.map_mk'_self, sup_bot_eq]
      rw [heq]
      exact hMn.map π (QuotientGroup.mk'_surjective _)
  refine ⟨fun u hu hu1 w hw hw1 => ?_, fun w hw hw1 => (key w hw hw1).1⟩
  set X := Subgroup.centralizer ({w} : Set G) with hXdef
  set C := Subgroup.centralizer ({u} : Set G) with hCdef
  have hconj : ∀ c ∈ X ⊓ C, ∀ y ∈ oddCoreOf C ⊓ X, c * y * c⁻¹ ∈ oddCoreOf C ⊓ X :=
    fun c hc y hy =>
      ⟨conj_mem_oddCoreOf hc.2 hy.1, X.mul_mem (X.mul_mem hc.1 hy.2) (X.inv_mem hc.1)⟩
  refine le_oddCoreOf (hUC w hw) hUel.1 (key w hw hw1).2 hu (hUel.2 u hu) inf_le_right
    ((odd_card_oddCoreOf C).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
    (inf_le_left.trans (Subgroup.map_subtype_le _)) fun c hc => ?_
  refine mem_normalizer_of_conj_mem (hconj c hc) fun y hy => ?_
  have := hconj c⁻¹ (inv_mem hc) y hy
  rwa [inv_inv] at this

end CFSG.Goldschmidt
