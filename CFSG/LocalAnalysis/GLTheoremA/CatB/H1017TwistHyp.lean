module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017SylowQ
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1114

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open

variable {K : Type} [Group K] [Finite K]

theorem noTwist_of_hyperCent {r : ℕ} (hr : 1 ≤ r)
    (h : ∀ E D : Subgroup K, IsElemAbelian 3 E → Nat.card E = 3 ^ r → D ≤ E →
      Nat.card D = 3 ^ (r - 1) → ∀ T : Subgroup K, IsPGroup 2 T →
      T ≤ Subgroup.centralizer (D : Set K) → E ≤ Subgroup.normalizer (T : Set K) →
      ∀ e ∈ E, ∀ t ∈ T, e * t = t * e)
    (E₀ : Subgroup K) (hE₀ : IsElemAbelian 3 E₀) (hcard : 3 ^ r ≤ Nat.card E₀) (T : Subgroup K)
    (hT : IsPGroup 2 T) (hET : E₀ ≤ Subgroup.normalizer (T : Set K)) :
    ∀ e ∈ E₀, ∀ t ∈ T, e * t = t * e := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro e he t ht
  have hE₀p : IsPGroup 3 E₀ := fun g => ⟨1, Subtype.ext (by simpa using hE₀.2 g g.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hE₀p
  have hrn : r ≤ n := by
    rw [hn] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hcard
  have hze : Nat.card (Subgroup.zpowers e) ∣ 3 ^ r := by
    rw [Nat.card_zpowers]
    exact (orderOf_dvd_of_pow_eq_one (hE₀.2 e he)).trans (dvd_pow_self 3 (by omega))
  obtain ⟨E, hEcard, hzE, hEE₀⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three hze
    (show 3 ^ r ∣ Nat.card E₀ from hn ▸ Nat.pow_dvd_pow 3 hrn)
    ((Subgroup.zpowers_le).2 he)
  have heE : e ∈ E := hzE (Subgroup.mem_zpowers e)
  have hE : IsElemAbelian 3 E := CFSG.Open.IsElemAbelian.mono hE₀ hEE₀
  have hEne : E ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hEcard
    have : 3 ≤ 3 ^ r := Nat.le_self_pow (by omega) 3
    omega
  have hT3 : ¬ 3 ∣ Nat.card T := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hT
    rw [hk]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow hd)
    omega
  have hgen := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1114.gen_by_hyperplanes
    Nat.prime_three hE hEne (hEE₀.trans hET) hT3
  have hcent : ∀ D : Subgroup K, D ≤ E ∧ (D.subgroupOf E).index = 3 →
      T ⊓ Subgroup.centralizer (D : Set K) ≤ Subgroup.centralizer (E : Set K) := by
    rintro D ⟨hDE, hDi⟩ x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hDcard : Nat.card D = 3 ^ (r - 1) := by
      have h1 := (D.subgroupOf E).card_mul_index
      rw [hDi, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDE).toEquiv, hEcard] at h1
      have : 3 ^ r = 3 ^ (r - 1) * 3 := by rw [← pow_succ]; congr 1; omega
      rw [this] at h1
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
    have haD : ∀ b ∈ E, b ∈ Subgroup.centralizer (D : Set K) := fun b hb => by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact comm_of_isElemAbelian' hE (hDE hd) hb
    have hN : E ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (D : Set K) : Subgroup K) :
        Set K) := by
      intro b hb
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hbT := Subgroup.mem_normalizer_iff.1 (hEE₀.trans hET hb) y
      constructor
      · rintro ⟨hyT, hyD⟩
        exact ⟨hbT.1 hyT, Subgroup.mul_mem _ (Subgroup.mul_mem _ (haD b hb) hyD)
          (Subgroup.inv_mem _ (haD b hb))⟩
      · rintro ⟨hyT, hyD⟩
        refine ⟨hbT.2 hyT, ?_⟩
        have : y = b⁻¹ * (b * y * b⁻¹) * b := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (haD b hb)) hyD)
          (haD b hb)
    exact h E D hE hEcard hDE hDcard _ (hT.to_le inf_le_left) inf_le_right hN a ha x hx
  have hTE : T ≤ Subgroup.centralizer (E : Set K) :=
    hgen.trans (iSup₂_le fun D hD => hcent D hD)
  exact (Subgroup.mem_centralizer_iff.1 (hTE ht) e heE)

omit [Finite K] in
theorem conj_mem_centerInf_of_normalizer {T : Subgroup K} {e : K}
    (he : e ∈ Subgroup.normalizer (T : Set K)) {z : K}
    (hz : z ∈ T ⊓ Subgroup.centralizer (T : Set K)) :
    e * z * e⁻¹ ∈ T ⊓ Subgroup.centralizer (T : Set K) := by
  refine ⟨(Subgroup.mem_normalizer_iff.1 he z).1 hz.1, Subgroup.mem_centralizer_iff.2 ?_⟩
  intro y hy
  have hy' : e⁻¹ * y * e ∈ T := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ he) y).1 hy
    simpa using this
  have hc := Subgroup.mem_centralizer_iff.1 hz.2 _ hy'
  calc y * (e * z * e⁻¹) = e * ((e⁻¹ * y * e) * z) * e⁻¹ := by group
    _ = e * (z * (e⁻¹ * y * e)) * e⁻¹ := by rw [hc]
    _ = e * z * e⁻¹ * y := by group

theorem exists_central_involution_split {T : Subgroup K} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    {e : K} (he3 : e ^ 3 = 1) (he : e ∈ Subgroup.normalizer (T : Set K)) :
    (∃ z ∈ T ⊓ Subgroup.centralizer (T : Set K), orderOf z = 2 ∧ e * z = z * e) ∨
    (∃ v ∈ T ⊓ Subgroup.centralizer (T : Set K), orderOf v = 2 ∧ e * v * e⁻¹ ≠ v ∧
      v * (e * v * e⁻¹) * (e ^ 2 * v * (e ^ 2)⁻¹) = 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := T ⊓ Subgroup.centralizer (T : Set K) with hZ
  haveI : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).2 hT1
  haveI : Nontrivial (Subgroup.center T) := hT.center_nontrivial
  obtain ⟨c, hc1⟩ := exists_ne (1 : Subgroup.center T)
  set g : K := ((c : T) : K) with hgdef
  have hg1 : g ≠ 1 := fun h1 => hc1 (Subtype.ext (Subtype.ext h1))
  have hgZ : g ∈ Z := ⟨(c : T).2, Subgroup.mem_centralizer_iff.2 fun y hy => by
    have := (Subgroup.mem_center_iff.1 c.2) ⟨y, hy⟩
    have h' := congrArg (fun u : T => (u : K)) this
    simp only [Subgroup.coe_mul] at h'
    first | exact h' | exact h'.symm⟩
  have hZ2 : IsPGroup 2 Z := hT.to_le inf_le_left
  have hZne : Z ≠ ⊥ := fun hb => hg1 ((Subgroup.mem_bot).1 (hb ▸ hgZ))
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hZ2
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    exact hZne (Subgroup.card_eq_one.1 hm)
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 (by rw [hm]; exact dvd_pow_self 2 hm0)
  have hvo : orderOf (v : K) = 2 := by rw [Subgroup.orderOf_coe, hv]
  by_cases hfix : e * (v : K) = v * e
  · exact Or.inl ⟨v, v.2, hvo, hfix⟩
  have hcomm : ∀ {a b : K}, a ∈ Z → b ∈ Z → a * b = b * a := fun ha hb =>
    (Subgroup.mem_centralizer_iff.1 hb.2 _ ha.1)
  have hv1 : e * (v : K) * e⁻¹ ∈ Z := conj_mem_centerInf_of_normalizer he v.2
  have hv2 : e ^ 2 * (v : K) * (e ^ 2)⁻¹ ∈ Z :=
    conj_mem_centerInf_of_normalizer (Subgroup.pow_mem _ he 2) v.2
  set w := (v : K) * (e * v * e⁻¹) * (e ^ 2 * v * (e ^ 2)⁻¹) with hw
  have hwZ : w ∈ Z := Subgroup.mul_mem _ (Subgroup.mul_mem _ v.2 hv1) hv2
  have hsq : ∀ {a : K}, a ∈ Z → a ^ 2 = 1 → ∀ {b : K}, b ∈ Z → b ^ 2 = 1 → (a * b) ^ 2 = 1 :=
    fun ha ha2 _ hb hb2 => by rw [(Commute.mul_pow (hcomm ha hb) 2), ha2, hb2, one_mul]
  have hv2' : (v : K) ^ 2 = 1 := by rw [← hvo]; exact pow_orderOf_eq_one _
  have hconj2 : ∀ g : K, (g * (v : K) * g⁻¹) ^ 2 = 1 := fun g => by
    rw [conj_pow, hv2', mul_one, mul_inv_cancel]
  have hw2 : w ^ 2 = 1 := hsq (Subgroup.mul_mem _ v.2 hv1) (hsq v.2 hv2' hv1 (hconj2 e)) hv2
    (hconj2 _)
  have he3' : e ^ 3 * (v : K) * (e ^ 3)⁻¹ = v := by rw [he3]; group
  have hwe : e * w * e⁻¹ = w := by
    have e1 : e * w * e⁻¹ = (e * v * e⁻¹) * (e ^ 2 * v * (e ^ 2)⁻¹) *
        (e ^ 3 * v * (e ^ 3)⁻¹) := by rw [hw]; group
    rw [e1, he3']
    have hc1 := hcomm (Subgroup.mul_mem _ hv1 hv2) v.2
    rw [hc1, hw]
    group
  by_cases hw1 : w = 1
  · refine Or.inr ⟨v, v.2, hvo, fun h => hfix ?_, hw1⟩
    calc e * (v : K) = e * v * e⁻¹ * e := by group
      _ = v * e := by rw [h]
  · refine Or.inl ⟨w, hwZ, ?_, ?_⟩
    · exact orderOf_eq_prime hw2 hw1
    · calc e * w = e * w * e⁻¹ * e := by group
        _ = w * e := by rw [hwe]

end CFSG.LocalAnalysis.GLTheoremA.H1017

end
