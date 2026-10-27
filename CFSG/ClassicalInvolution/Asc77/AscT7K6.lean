module

public import CFSG.ClassicalInvolution.Asc77.AscT7DRS
public import CFSG.ClassicalInvolution.Asc77.WP3Layer

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance.Bootstrap

namespace T7K

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}

theorem sq_eq_of_mul_involution (hs : Hyp23Setting p f Ω K K' z) {R R' : Subgroup G}
    (hR : IsSylow2In R K) (hR' : IsSylow2In R' K') (hc : Commutes R R') {a b : G} (ha : a ∈ R)
    (hb : b ∈ R') (hu2 : (a * b) * (a * b) = 1) (hu1 : a * b ≠ 1) (huz : a * b ≠ z) :
    a * a = z ∧ b * b = z := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hKΩ : K ∈ Ω := hs.stand.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK : IsUniqueInvolution K z := hs.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hcab : a * b = b * a := hc a ha b hb
  have hsq : (a * a) * (b * b) = 1 := by
    calc (a * a) * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [hcab]
      _ = (a * b) * (a * b) := by group
      _ = 1 := hu2
  have haL : a ∈ K := hR.1 ha
  have hbL' : b ∈ K' := hR'.1 hb
  have hcard : Nat.card ↥(R ⊓ R') ≤ 2 :=
    hΩ.card_le_two_of_le_inf hKΩ hK'Ω hs.hne.symm (hR.2.1.to_le inf_le_left)
      (inf_le_left.trans hR.1) (inf_le_right.trans hR'.1)
  have hA : ∀ x ∈ R ⊓ R', x * x = 1 := by
    intro x hx
    have hd : orderOf x ∣ Nat.card ↥(R ⊓ R') := Subgroup.orderOf_dvd_natCard _ hx
    have hpos : 0 < Nat.card ↥(R ⊓ R') := Nat.card_pos
    have h2 : orderOf x ∣ 2 := by
      interval_cases hc2 : Nat.card ↥(R ⊓ R')
      · exact hd.trans (one_dvd 2)
      · exact hd
    have := orderOf_dvd_iff_pow_eq_one.mp h2
    rwa [pow_two] at this
  have haaA : a * a ∈ R ⊓ R' := by
    refine ⟨R.mul_mem ha ha, ?_⟩
    have : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    rw [this]
    exact R'.inv_mem (R'.mul_mem hb hb)
  have haa2 : (a * a) * (a * a) = 1 := hA _ haaA
  have haa : a * a = z := by
    rcases hzK.unique (a * a) (K.mul_mem haL haL) haa2 with h | h
    · exfalso
      have hbb : b * b = 1 := by rwa [h, one_mul] at hsq
      have ha1 : a = 1 ∨ a = z := hzK.unique a haL h
      have hb1 : b = 1 ∨ b = z := hzK'.unique b hbL' hbb
      rcases ha1 with h1 | h1 <;> rcases hb1 with h2 | h2
      · exact hu1 (by rw [h1, h2, one_mul])
      · exact huz (by rw [h1, h2, one_mul])
      · exact huz (by rw [h1, h2, mul_one])
      · exact hu1 (by rw [h1, h2]; exact hzK.sq)
    · exact h
  refine ⟨haa, ?_⟩
  have h1 : b * b = z⁻¹ := eq_inv_of_mul_eq_one_right (by rwa [haa] at hsq)
  rw [h1]
  exact inv_eq_of_mul_eq_one_right hzK.sq

theorem exists_decomp (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    ∃ (R R' : Subgroup G) (a b r : G), IsSylow2In R K ∧ IsSylow2In R' K' ∧ Commutes R R' ∧
      R ≤ Subgroup.normalizer (W : Set G) ∧ R' ≤ Subgroup.normalizer (W : Set G) ∧
      a ∈ R ∧ b ∈ R' ∧ a ∈ W ∧ b ∈ W ∧ u = a * b ∧ a * a = z ∧ b * b = z ∧
      r ∈ R ∧ r * u * r⁻¹ = u * z := by
  have hst := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK : IsUniqueInvolution K z := hs.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨S, R, R', hWS, hR, hR', hRS, hR'S⟩ := T7D.exists_sylow_frame hs hd.hW hd.hzW
  have hRD : R ∈ DSet Ω W :=
    Thompson.mem_DSet_of_le_sylow hp hq hΩ hd.hW hWS (mem_RSet_of_isSylow2In hKΩ hR) hRS
  have hR'D : R' ∈ DSet Ω W :=
    Thompson.mem_DSet_of_le_sylow hp hq hΩ hd.hW hWS (mem_RSet_of_isSylow2In hK'Ω hR') hR'S
  have h2 : IsPGroup 2 ↥(R ⊔ R') := (Sylow.isPGroup' S).to_le (sup_le hRS hR'S)
  have hc : Commutes R R' :=
    hΩ.commutes_of_twin_of_isPGroup hKΩ hK'Ω hs.hne.symm hzK hzK' hR.1 hR'.1 h2
  have hQ : IsSylow2In (R ⊔ R') (K ⊔ K') :=
    T7A.isSylow2In_sup_of_twin hp hΩ hKΩ hK'Ω hs.hne hzK hzK' hR hR' hc
  have hS2 : IsPGroup 2 ↥((S : Subgroup G) ⊓ (K ⊔ K')) := (Sylow.isPGroup' S).to_le inf_le_left
  have heq : (S : Subgroup G) ⊓ (K ⊔ K') = R ⊔ R' :=
    hQ.eq_of_le hS2 inf_le_right (le_inf (sup_le hRS hR'S) hQ.1)
  have huRR' : u ∈ R ⊔ R' := by
    rw [← heq]
    exact ⟨hWS hd.huW, hd.hu⟩
  obtain ⟨a, ha, b, hb, hab⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hc huRR'
  have hu2' : (a * b) * (a * b) = 1 := by rw [hab]; exact hd.hu2
  have hsq := sq_eq_of_mul_involution hs hR hR' hc ha hb hu2' (by rw [hab]; exact hd.hu1)
    (by rw [hab]; exact hd.huz)
  have hWab := Thompson.commutes_of_mem_WSet hp hq hΩ hd.hW
  obtain ⟨hRW, -, hcyc, h4, -⟩ := Thompson.inf_W_of_mem_D hp hq hΩ hd.hW hRD hKΩ hR
  have haW : a ∈ W := by
    by_contra haW
    obtain ⟨v, hv, hv2⟩ := Thompson.exists_sq_ne_one hcyc (by omega)
    have hvKW : v ∈ K ⊓ W := by rw [← hRW]; exact hv
    have hinv : a * v * a⁻¹ = v⁻¹ :=
      Thompson.conj_eq_inv_of_mem_inf_W hp hq hΩ hd.hW hKΩ hRD hR ha haW hvKW
    have hvu : Commute v u := hWab v hv.2 u hd.huW
    have hvb : Commute v b := hc v hv.1 b hb
    have hva : Commute v a := by
      have : a = u * b⁻¹ := by rw [← hab]; group
      rw [this]
      exact hvu.mul_right hvb.inv_right
    have h5 : a * v * a⁻¹ = v := by
      rw [← hva.eq]
      group
    rw [h5] at hinv
    exact hv2 (by
      have : v * v = 1 := by
        calc v * v = v * v⁻¹ := by rw [← hinv]
          _ = 1 := mul_inv_cancel v
      exact this)
  have hbW : b ∈ W := by
    have : b = a⁻¹ * u := by rw [← hab]; group
    rw [this]
    exact W.mul_mem (W.inv_mem haW) hd.huW
  have hctx : Thompson.Ctx p f Ω W := T7D.ctx_of_stand hst hd.hW
  obtain ⟨ρ, hρK, hρR⟩ := T7D.exists_rep hp hq hΩ hd.hW hKΩ hR hRD
  obtain ⟨σ, hσK, hσR⟩ := T7D.exists_rep hp hq hΩ hd.hW hK'Ω hR' hR'D
  have hnbr : σ.K ∈ omegaNbr Ω ρ.K := by
    rw [hρK, hσK]
    have hperp : K' ∈ KPerp Ω K := by rw [hs.perp]; exact Or.inr rfl
    rcases hperp with h | h
    · exact absurd h hs.hne
    · exact h
  have haK : a ∈ ρ.K ⊓ W := ⟨by rw [hρK]; exact hR.1 ha, haW⟩
  have hbK : b ∈ σ.K ⊓ W := ⟨by rw [hσK]; exact hR'.1 hb, hbW⟩
  have h1 : ρ.r * a * ρ.r⁻¹ = a⁻¹ := hctx.conj_inv ρ haK
  have h3 : ρ.r * b = b * ρ.r := hctx.centralizes ρ σ hnbr hbK
  have hainv : a⁻¹ = a * z := by
    refine (eq_inv_of_mul_eq_one_right ?_).symm
    calc a * (a * z) = (a * a) * z := by group
      _ = z * z := by rw [hsq.1]
      _ = 1 := hzK.sq
  have hzb : z * b = b * z := hzK'.commute_of_mem (hR'.1 hb)
  refine ⟨R, R', a, b, ρ.r, hR, hR', hc, hRD.2, hR'D.2, ha, hb, haW, hbW, hab.symm, hsq.1, hsq.2,
    by rw [← hρR]; exact ρ.hr, ?_⟩
  have hrb : ρ.r * b * ρ.r⁻¹ = b := by
    rw [h3]
    group
  calc ρ.r * u * ρ.r⁻¹ = (ρ.r * a * ρ.r⁻¹) * (ρ.r * b * ρ.r⁻¹) := by rw [← hab]; group
    _ = (a * z) * b := by rw [h1, hrb, hainv]
    _ = a * (z * b) := by group
    _ = a * (b * z) := by rw [hzb]
    _ = u * z := by rw [← hab]; group

end T7K

end CFSG.ClassicalInvolution.Asc77
