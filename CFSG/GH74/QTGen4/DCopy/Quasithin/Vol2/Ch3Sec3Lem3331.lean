module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3StatementsB
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3331

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.Lem3328
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

@[expose] def Step3_3_31S_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsAltBlockType L 6 → T ≤ Subgroup.normalizer (L : Set G) → tC L T ≠ ⊥ →
    ∀ d ∈ D, d ∉ M → ¬ CFSG.conjugate (vPlus L T) d ≤ qL L T →
      (qL L T).relIndex (qL L T ⊔ CFSG.conjugate (vPlus L T) d) = 2 ∧
      d ∈ Subgroup.normalizer ((qL L T ⊔ CFSG.conjugate (vPlus L T) d : Subgroup G) : Set G) ∧
      CFSG.conjugate (vPlus L T) d ≤ Subgroup.centralizer (tC L T : Set G) ∧
      qL L T = vPlus L T ⊔
        (qL L T ⊓ Subgroup.centralizer (CFSG.conjugate (vPlus L T) d : Set G)) ∧
      T = T ⊓ L ⊔ qL L T ⊔ CFSG.conjugate (vPlus L T) d ∧
      Nat.card ↥(quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) = 2

@[expose] def Step3_3_31E4_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsAltBlockType L 6 → T ≤ Subgroup.normalizer (L : Set G) → tC L T ≠ ⊥ →
    ∀ d ∈ D, d ∉ M → ¬ CFSG.conjugate (vPlus L T) d ≤ qL L T →
      frattini ↥(qL L T) ≠ ⊥ → Nat.card ↥(tC L T) = 4 →
      Nonempty (↥(qL L T ⊔ CFSG.conjugate (vPlus L T) d) ≃* D8D8E4)

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

open Lem3331

variable {T M L D : Subgroup G}

namespace Hyp331

theorem frattini_qL_eq_bot_of_tC_ne_bot_F4
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h27 : Stmt3_3_27_F4)
    (hS : Step3_3_31S_F4) (hE4 : Step3_3_31E4_F4) (hA6 : IsAltBlockType L 6)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hTC : tC L T ≠ ⊥) {d : G} (hdD : d ∈ D)
    (hdM : d ∉ M) (hdV : ¬ CFSG.conjugate (vPlus L T) d ≤ qL L T) : frattini ↥(qL L T) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hF
  obtain ⟨-, hdS, hVdC, hQdec, hTdec, hZ2⟩ := hS G T M L D h hA6 hTL hTC d hdD hdM hdV
  obtain ⟨hTCd, hFTC, -⟩ := h27 G T M L D h d hdD hdM hdV hTC
  set Q := qL L T with hQdef
  set V := vPlus L T with hVdef
  set C := tC L T with hCdef
  set Vd := CFSG.conjugate V d with hVddef
  have hT2 : IsPGroup 2 ↥T := h.sylow.1
  have hQ2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQT : Q ≤ T := pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hCT : C ≤ T := inf_le_left
  have hCe : IsElemAbelian 2 C := isElemAbelian_of_frattini_eq_bot (hT2.to_le hCT) hFTC
  have hCab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := fun a ha b hb => by
    have := hCe.1
    exact setLike_mul_comm ha hb
  have hCQ : C ≤ Q := h.tC_le_qL h38 h39 hTL
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVQ : V ≤ Q := hred.1.trans inf_le_left
  have hVZ : ∀ v ∈ V, ∀ q ∈ Q, v * q = q * v := fun v hv q hq =>
    (Subgroup.mem_centralizer_iff.mp ((hred.1.trans inf_le_right) hv) q hq).symm
  have hVe := hred.2.1
  have hΦ : (frattini ↥Q).map Q.subtype ≤ C := h.frattini_qL_le_tC h38 h39 hA6.1 hTL
  have hsq : ∀ x ∈ Q, x ^ 2 ∈ C := fun x hx => sq_mem_of_frattini_le hQ2 hΦ hx
  have hCN : T ≤ Subgroup.normalizer (C : Set G) := le_normalizer_tC hTL
  have hVN : V ≤ Subgroup.normalizer (C : Set G) := (hVQ.trans hQT).trans hCN
  have hx₀ : ∃ x ∈ Q, x ^ 2 ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hF (frattini_eq_bot_of_isElemAbelian (isElemAbelian_of_sq_eq_one hall))
  have hCVe : ∀ x ∈ C ⊔ V, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨c, hc, v, hv, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hVN).mp hx
    have hcv : Commute c v := (hVZ v hv c (hCQ hc)).symm
    rw [hcv.mul_pow, hCe.2 c hc, hVe.2 v hv, one_mul]
  have hCVQ : C ⊔ V ≤ Q := sup_le hCQ hVQ
  have hlt : ¬ Q ≤ C ⊔ V := fun hle => by
    obtain ⟨x, hx, hx2⟩ := hx₀
    exact hx2 (hCVe x (hle hx))
  obtain ⟨u, ⟨huQ, huVd⟩, huCV⟩ : ∃ u ∈ Q ⊓ Subgroup.centralizer (Vd : Set G), u ∉ C ⊔ V := by
    by_contra hcon
    push Not at hcon
    apply hlt
    rw [hQdec]
    exact sup_le le_sup_right fun x hx => hcon x hx
  have hidx2 : (C ⊔ V).relIndex Q = 2 := by
    have hU := h.blockU_le_vPlus h38 h39 hA6.1 hTL
    have h1 : (blockU L ⊔ C).relIndex Q ≤ 2 := h.relIndex_qL_le_two h38 h39 hA6 hTL
    have h2 : (C ⊔ V).relIndex Q ≤ (blockU L ⊔ C).relIndex Q := by
      rw [sup_comm C V]
      exact Subgroup.relIndex_le_of_le_left (sup_le_sup_right hU C)
        Subgroup.index_ne_zero_of_finite
    have h3 : (C ⊔ V).relIndex Q ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      exact hlt
    have h4 : (C ⊔ V).relIndex Q ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hu2 : u ^ 2 ∈ C ⊔ V := by
    have h2 : ((C ⊔ V).subgroupOf Q).index = 2 := hidx2
    have h3 := (Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨u, huQ⟩ : ↥Q))
      (b := ⟨u, huQ⟩)).mpr Iff.rfl
    rw [pow_two]
    exact Subgroup.mem_subgroupOf.mp h3
  have hQgen : Q = Subgroup.zpowers u ⊔ (C ⊔ V) := by
    have hle : Subgroup.zpowers u ⊔ (C ⊔ V) ≤ Q := sup_le (Subgroup.zpowers_le.mpr huQ) hCVQ
    refine le_antisymm (fun x hx => ?_) hle
    by_cases hxW : x ∈ C ⊔ V
    · exact Subgroup.mem_sup_right hxW
    · have h2 : ((C ⊔ V).subgroupOf Q).index = 2 := hidx2
      have h3 := (Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨u, huQ⟩ : ↥Q)⁻¹)
        (b := ⟨x, hx⟩)).mpr (iff_of_false (fun h' => huCV (by
          have := Subgroup.mem_subgroupOf.mp h'
          simpa using this)) (fun h' => hxW (Subgroup.mem_subgroupOf.mp h')))
      have h4 : u⁻¹ * x ∈ C ⊔ V := Subgroup.mem_subgroupOf.mp h3
      have h5 : x = u * (u⁻¹ * x) := by group
      rw [h5]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))
        (Subgroup.mem_sup_right h4)
  have huN : u ∈ Subgroup.normalizer (C : Set G) := hCN (hQT huQ)
  have hu2C : ∀ c ∈ C, u ^ 2 * c = c * u ^ 2 := by
    intro c hc
    obtain ⟨c₁, hc₁, v, hv, he⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hVN).mp hu2
    rw [he]
    have h1 : c₁ * c = c * c₁ := hCab c₁ hc₁ c hc
    have h2 : v * c = c * v := hVZ v hv c (hCQ hc)
    calc c₁ * v * c = c₁ * (v * c) := by group
      _ = c₁ * (c * v) := by rw [h2]
      _ = c * c₁ * v := by rw [← mul_assoc, h1]
      _ = c * (c₁ * v) := by group
  have hcentT : C ⊓ Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer (T : Set G) := by
    intro c hc
    have hcC : c ∈ C := hc.1
    have hcu : c * u = u * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
    have hcL : c ∈ Subgroup.centralizer (L : Set G) := (Subgroup.mem_inf.mp hcC).2
    have hle : T ≤ Subgroup.centralizer ({c} : Set G) := by
      rw [hTdec]
      refine sup_le (sup_le ?_ ?_) ?_
      · intro t ht
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hcL t ht.2)
      · rw [hQgen]
        refine sup_le (Subgroup.zpowers_le.mpr ?_) (sup_le ?_ ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact hcu.symm
        · intro c' hc'
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact hCab c' hc' c hcC
        · intro v hv
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact hVZ v hv c (hCQ hcC)
      · intro w hw
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp (hVdC hw) c hcC).symm
    exact Subgroup.mem_centralizer_iff.mpr fun t ht =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hle ht))
  have hCuZ : C ⊓ Subgroup.centralizer ({u} : Set G) ≤
      quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) := by
    intro c hc
    refine ⟨Subgroup.subset_closure ⟨⟨hCT hc.1, hcentT hc⟩, hCe.2 c hc.1⟩,
      (Subgroup.mem_inf.mp hc.1).2⟩
  have hCu2 : Nat.card ↥(C ⊓ Subgroup.centralizer ({u} : Set G)) ≤ 2 := by
    rw [← hZ2]
    exact Subgroup.card_le_of_le hCuZ
  have hC4 : Nat.card ↥C ≤ 4 := by
    have h1 := card_le_sq_of_centralizes hCe huN hu2C
    have h2 : Nat.card ↥(C ⊓ Subgroup.centralizer ({u} : Set G)) ^ 2 ≤ 4 :=
      calc Nat.card ↥(C ⊓ Subgroup.centralizer ({u} : Set G)) ^ 2 ≤ 2 ^ 2 :=
            Nat.pow_le_pow_left hCu2 2
        _ = 4 := by norm_num
    exact h1.trans h2
  obtain ⟨k, hk⟩ := (hT2.to_le hCT).exists_card_eq
  have hC1 : 1 < Nat.card ↥C := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    exact hTC
  have hk12 : k = 1 ∨ k = 2 := by
    rcases k with _ | _ | _ | k
    · rw [hk] at hC1; norm_num at hC1
    · left; rfl
    · right; rfl
    · exfalso
      rw [hk] at hC4
      have h8 : 8 ≤ 2 ^ (k + 1 + 1 + 1) :=
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (k + 1 + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  have hodd : Odd (orderOf d) := by
    have h1 : orderOf (⟨d, hdD⟩ : ↥D) ∣ Nat.card ↥D := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat h.Dodd h1
  have hfin : d ∈ Subgroup.normalizer (C : Set G) → False := by
    intro hdC
    apply hTC
    rw [← hTCd]
    refine le_antisymm (le_inf le_rfl fun c hc => ?_) inf_le_left
    show c ∈ C.map (MulAut.conj d⁻¹).toMonoidHom
    rw [A38.mem_map_conj, inv_inv]
    exact (Subgroup.mem_normalizer_iff.mp hdC c).mp hc
  rcases hk12 with rfl | rfl
  ·
    have hk2 : Nat.card ↥C = 2 := by rw [hk, pow_one]
    have hCcen : ∀ t ∈ T, ∀ c ∈ C, t * c = c * t := by
      intro t ht c hc
      by_cases hc1 : c = 1
      · rw [hc1, mul_one, one_mul]
      have h1 : t * c * t⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp (hCN ht) c).mp hc
      have h2 : t * c * t⁻¹ ≠ 1 := fun h' => hc1 (by
        have := congrArg (fun z => t⁻¹ * z * t) h'
        simpa [mul_assoc] using this)
      have h3 : (⟨t * c * t⁻¹, h1⟩ : ↥C) = ⟨c, hc⟩ :=
        eq_of_card_two hk2 (fun h' => h2 (congrArg Subtype.val h'))
          (fun h' => hc1 (congrArg Subtype.val h'))
      have h4 : t * c * t⁻¹ = c := congrArg Subtype.val h3
      calc t * c = t * c * t⁻¹ * t := by group
        _ = c * t := by rw [h4]
    have huQc : ∀ q ∈ Q, u * q = q * u := by
      intro q hq
      have hle : Q ≤ Subgroup.centralizer ({u} : Set G) := by
        rw [hQgen]
        refine sup_le (Subgroup.zpowers_le.mpr ?_) (sup_le ?_ ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
        · intro c hc
          exact Subgroup.mem_centralizer_singleton_iff.mpr (hCcen u (hQT huQ) c hc).symm
        · intro v hv
          exact Subgroup.mem_centralizer_singleton_iff.mpr (hVZ v hv u huQ)
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hq)).symm
    have hu21 : u ^ 2 ≠ 1 := by
      intro hu1
      obtain ⟨x, hx, hx2⟩ := hx₀
      apply hx2
      rw [hQgen] at hx
      have hWN : C ⊔ V ≤ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G) : Set G) := by
        intro w hw
        rw [Subgroup.mem_normalizer_iff]
        intro z
        have hwu : w * u = u * w := (huQc w (hCVQ hw)).symm
        constructor
        · rintro ⟨n, rfl⟩
          refine ⟨n, ?_⟩
          change u ^ n = w * u ^ n * w⁻¹
          rw [(Commute.zpow_right hwu n).eq]
          group
        · rintro ⟨n, hn⟩
          have hn' : u ^ n = w * z * w⁻¹ := hn
          refine ⟨n, ?_⟩
          have hc := (Commute.zpow_right hwu n).eq
          calc u ^ n = w⁻¹ * (w * u ^ n) := by group
            _ = w⁻¹ * (u ^ n * w) := by rw [hc]
            _ = w⁻¹ * (w * z * w⁻¹ * w) := by rw [hn']
            _ = z := by group
      obtain ⟨y, ⟨n, rfl⟩, w, hw, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hWN).mp hx
      have hwu : w * u = u * w := (huQc w (hCVQ hw)).symm
      have hc : Commute (u ^ n) w := Commute.zpow_left hwu.symm n
      have hun2 : (u ^ n) ^ 2 = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu1, one_zpow]
      rw [hc.mul_pow, hun2, one_mul, hCVe w hw]
    have hSu : Q ⊔ Vd ≤ Subgroup.centralizer ({u} : Set G) := by
      refine sup_le (fun q hq => Subgroup.mem_centralizer_singleton_iff.mpr (huQc q hq).symm) ?_
      intro w hw
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp huVd w hw)
    have hduQ : d * u * d⁻¹ ∈ Q := by
      have hSN : d⁻¹ ∈ Subgroup.normalizer ((Q ⊔ Vd : Subgroup G) : Set G) :=
        Subgroup.inv_mem _ hdS
      have hdu : d * u * d⁻¹ ∈ Q ⊔ Vd :=
        (Subgroup.mem_normalizer_iff.mp hdS u).mp (Subgroup.mem_sup_left huQ)
      have hC : (Q ⊔ Vd) ⊓ Subgroup.centralizer (Q : Set G) ≤ Q := by
        intro x hx
        have hcv : T ⊓ Subgroup.centralizer (vPlus L T : Set G) = qL L T :=
          (h.centralizer_vPlus h38 h39).2.1
        show x ∈ qL L T
        rw [← hcv]
        exact ⟨(sup_le hQT (Hyp331.map_conj_le_of_le (hVQ.trans hQT)
          (Subgroup.inv_mem _ (h.DN hdD)))) hx.1,
          Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hVQ) hx.2⟩
      refine hC ⟨hdu, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
      have h1 : d⁻¹ * q * d ∈ Q ⊔ Vd := by
        have := (Subgroup.mem_normalizer_iff.mp hSN q).mp (Subgroup.mem_sup_left hq)
        simpa using this
      have h2 : u * (d⁻¹ * q * d) = (d⁻¹ * q * d) * u :=
        (Subgroup.mem_centralizer_singleton_iff.mp (hSu h1)).symm
      calc q * (d * u * d⁻¹) = d * ((d⁻¹ * q * d) * u) * d⁻¹ := by group
        _ = d * (u * (d⁻¹ * q * d)) * d⁻¹ := by rw [h2]
        _ = d * u * d⁻¹ * q := by group
    have hu2C' : u ^ 2 ∈ C := hsq u huQ
    have hdu2 : d * u ^ 2 * d⁻¹ ∈ C := by
      have := hsq _ hduQ
      rwa [conj_pow] at this
    have hdu2' : d * u ^ 2 * d⁻¹ = u ^ 2 := by
      have h1 : (⟨d * u ^ 2 * d⁻¹, hdu2⟩ : ↥C) = ⟨u ^ 2, hu2C'⟩ :=
        eq_of_card_two hk2 (fun h' => hu21 (by
          have := congrArg Subtype.val h'
          have h2 : d * u ^ 2 * d⁻¹ = 1 := this
          have := congrArg (fun z => d⁻¹ * z * d) h2
          simpa [mul_assoc] using this)) (fun h' => hu21 (congrArg Subtype.val h'))
      exact congrArg Subtype.val h1
    apply hfin
    rw [Subgroup.mem_normalizer_iff]
    intro c
    have hall : ∀ c ∈ C, c = 1 ∨ c = u ^ 2 := by
      intro c hc
      by_cases hc1 : c = 1
      · exact Or.inl hc1
      · right
        have := eq_of_card_two hk2 (x := (⟨c, hc⟩ : ↥C)) (y := ⟨u ^ 2, hu2C'⟩)
          (fun h' => hc1 (congrArg Subtype.val h')) (fun h' => hu21 (congrArg Subtype.val h'))
        exact congrArg Subtype.val this
    constructor
    · intro hc
      rcases hall c hc with rfl | rfl
      · simp
      · rw [hdu2']
        exact hu2C'
    · intro hc
      rcases hall _ hc with h1 | h1
      · have : c = 1 := by
          have := congrArg (fun z => d⁻¹ * z * d) h1
          simpa [mul_assoc] using this
        rw [this]
        exact C.one_mem
      · have : c = u ^ 2 := by
          have h2 : d * c * d⁻¹ = d * u ^ 2 * d⁻¹ := by rw [h1, hdu2']
          have := congrArg (fun z => d⁻¹ * z * d) h2
          simpa [mul_assoc] using this
        rw [this]
        exact hu2C'
  ·
    have hk4 : Nat.card ↥C = 4 := by rw [hk]; norm_num
    obtain ⟨e⟩ := hE4 G T M L D h hA6 hTL hTC d hdD hdM hdV hF hk4
    obtain ⟨x, hx, hx2⟩ := hx₀
    set S := Q ⊔ Vd with hSdef
    have hxS : x ∈ S := Subgroup.mem_sup_left hx
    set α : MulAut ↥S := S.normalizerMonoidHom ⟨d, hdS⟩ with hα
    have hαodd : Odd (orderOf α) := by
      have h1 : orderOf α ∣ orderOf (⟨d, hdS⟩ : ↥(Subgroup.normalizer (S : Set G))) :=
        orderOf_map_dvd _ _
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat hodd h1
    have hfix := fixes_sq_of_odd e α hαodd ⟨x, hxS⟩
    have h1 : d * x ^ 2 * d⁻¹ = x ^ 2 := congrArg Subtype.val hfix
    have hx2C : x ^ 2 ∈ C := hsq x hx
    have hmem : x ^ 2 ∈ C ⊓ CFSG.conjugate C d := by
      refine ⟨hx2C, ?_⟩
      show x ^ 2 ∈ C.map (MulAut.conj d⁻¹).toMonoidHom
      rw [A38.mem_map_conj, inv_inv, h1]
      exact hx2C
    rw [hTCd, Subgroup.mem_bot] at hmem
    exact hx2 hmem

end Hyp331

theorem stmt3_3_31_of_F4
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h14 : Stmt3_3_14_F4) (h26 : Stmt3_3_26_F4)
    (h27 : Stmt3_3_27_F4) (h30 : Stmt3_3_30_F4) (hS : Step3_3_31S_F4) (hE4 : Step3_3_31E4_F4) :
    Stmt3_3_31_F4 := by
  intro G _ _ T M L D h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hTC
  obtain ⟨-, hML⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hML
  have hA6 := h30 G T M L D h
  obtain ⟨d, hdD, hdM, hdV⟩ := h26 G T M L D h
  obtain ⟨hidx, hdS, -⟩ := hS G T M L D h hA6 hTL hTC d hdD hdM hdV
  have hF := h.frattini_qL_eq_bot_of_tC_ne_bot_F4 h38 h39 h27 hS hE4 hA6 hTL hTC hdD hdM hdV
  have hQe : IsElemAbelian 2 (qL L T) :=
    isElemAbelian_of_frattini_eq_bot (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hF
  have hQT : qL L T ≤ T := pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVQ : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  have hdT : d ∈ Subgroup.normalizer (T : Set G) := h.DN hdD
  have hVdT : CFSG.conjugate (vPlus L T) d ≤ T :=
    Hyp331.map_conj_le_of_le (hVQ.trans hQT) (Subgroup.inv_mem _ hdT)
  have hST : qL L T ⊔ CFSG.conjugate (vPlus L T) d ≤ T := sup_le hQT hVdT
  have hCQ : T ⊓ Subgroup.centralizer (vPlus L T : Set G) = qL L T :=
    (h.centralizer_vPlus h38 h39).2.1
  have hSC : (qL L T ⊔ CFSG.conjugate (vPlus L T) d) ⊓ Subgroup.centralizer (qL L T : Set G) ≤
      qL L T := fun x hx => by
    rw [← hCQ]
    exact ⟨hST hx.1, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hVQ) hx.2⟩
  obtain ⟨hQmax, huniq⟩ := isMaxElemAbelian_of_relIndex_two le_sup_left hQe hidx hSC
  have hodd : Odd (orderOf d) := by
    have h1 : orderOf (⟨d, hdD⟩ : ↥D) ∣ Nat.card ↥D := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat h.Dodd h1
  have hdQ := mem_normalizer_of_odd_of_unique hQmax huniq hdS hodd
  exact hdM (h.toSetup331.normalizer_le h38 h39 h.toSetup331.pCoreOf_ne_bot
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _) hdQ)

end CFSG.Quasithin.H13
