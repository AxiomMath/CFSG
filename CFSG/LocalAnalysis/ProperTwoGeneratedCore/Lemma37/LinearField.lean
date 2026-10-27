module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.LinearAbelian
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.LinearLift
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerLinearMul

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {z : G}

@[expose] noncomputable def sylowTorusAction (hz : IsCentralInvolution (S : Subgroup G) z)
    {D : Subgroup (EscapingQuotient z)}
    (hDN : D ≤ Subgroup.normalizer (((sylowBar hz).range : Subgroup (EscapingQuotient z)) :
      Set (EscapingQuotient z))) :
    D →* MulAut (S : Subgroup G) :=
  (MulAut.congr (MonoidHom.ofInjective (sylowBar_injective hz)).symm).toMonoidHom.comp
    (((sylowBar hz).range.normalizerMonoidHom).comp (Subgroup.inclusion hDN))

theorem sylowBar_sylowTorusAction (hz : IsCentralInvolution (S : Subgroup G) z)
    {D : Subgroup (EscapingQuotient z)}
    (hDN : D ≤ Subgroup.normalizer (((sylowBar hz).range : Subgroup (EscapingQuotient z)) :
      Set (EscapingQuotient z))) (d : D) (s : (S : Subgroup G)) :
    sylowBar hz (sylowTorusAction hz hDN d s) = d * sylowBar hz s * (d : EscapingQuotient z)⁻¹ := by
  change sylowBar hz ((MonoidHom.ofInjective (sylowBar_injective hz)).symm
    ((sylowBar hz).range.normalizerMonoidHom ⟨d, hDN d.2⟩
      (MonoidHom.ofInjective (sylowBar_injective hz) s))) = _
  rw [MonoidHom.apply_ofInjective_symm]
  rfl

variable {H : Subgroup G} (hset : CoreSetting G S H) (hz : IsCentralInvolution (S : Subgroup G) z)
  (hesc : ¬ Subgroup.centralizer ({z} : Set G) ≤ H) {J : Subgroup (EscapingQuotient z)}
  (hJ : CFSG.IsComponent J) (hzJ : escapingBar z ∉ J) {D : Subgroup (EscapingQuotient z)} {q : ℕ}
  (hlin : LinearSylowData J ((sylowBar hz).range ⊓ J) D q)
include hset hz hesc hJ hzJ hlin

theorem caseOne_torus_le_normalizer :
    D ≤ Subgroup.normalizer (((sylowBar hz).range : Subgroup (EscapingQuotient z)) :
      Set (EscapingQuotient z)) := by
  have hq := caseOne_quotientData hset hz hesc
  have hzS : escapingBar z ∈ (sylowBar hz).range := ⟨⟨z, hz.1⟩, rfl⟩
  intro d hd
  refine Subgroup.mem_normalizer_fintype fun s hs => ?_
  rcases caseOne_sylowBar_mem_or hset hz hesc hJ hzJ hlin hs with h | h
  · exact (hlin.torus_conj d hd s ⟨hs, h⟩).1
  · have hc := hlin.torus_conj d hd _ ⟨(sylowBar hz).range.mul_mem hzS hs, h⟩
    have heq : d * s * d⁻¹ = escapingBar z * (d * (escapingBar z * s) * d⁻¹) := by
      have h1 : s = escapingBar z * (escapingBar z * s) := by
        rw [← mul_assoc, escapingBar_mul_self hz.2.1, one_mul]
      conv_lhs => rw [h1]
      rw [← mul_assoc d, (hq.commute_bar d).eq]
      group
    rw [heq]
    exact (sylowBar hz).range.mul_mem hzS hc.1

theorem caseOne_field_eq_four {n : ℕ} (hn : 2 ≤ n) (hq : q = 2 ^ n) : q = 4 := by
  have hquot := caseOne_quotientData hset hz hesc
  have hcomm := caseOne_sylow_comm hset hz hesc hJ hzJ hlin
  let _ : CommGroup (S : Subgroup G) :=
    { (inferInstance : Group (S : Subgroup G)) with
      mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  have hsq := caseOne_sylow_sq hset hz hesc hJ hzJ hlin
  have hS2 : ∀ s : (S : Subgroup G), s ^ 2 = 1 := fun s =>
    Subtype.ext (by rw [SubgroupClass.coe_pow, pow_two]; exact hsq s s.2)
  have hDN := caseOne_torus_le_normalizer hset hz hesc hJ hzJ hlin
  set Φ := sylowTorusAction hz hDN with hΦ
  set Y := ((S : Subgroup G).normalizerMonoidHom).range with hY
  have hR1 : ∃ x ∈ (sylowBar hz).range ⊓ J, x ≠ 1 := by
    have h1 : 1 < Nat.card ((sylowBar hz).range ⊓ J : Subgroup (EscapingQuotient z)) := by
      rw [hlin.card, hq]
      exact Nat.one_lt_two_pow (by omega)
    obtain ⟨⟨x, hx⟩, hx1⟩ :=
      (Subgroup.ne_bot_iff_exists_ne_one).mp ((Subgroup.one_lt_card_iff_ne_bot _).mp h1)
    exact ⟨x, hx, fun h => hx1 (Subtype.ext h)⟩
  have hΦinj : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro d hd
    obtain ⟨x₀, hx₀R, hx₀1⟩ := hR1
    obtain ⟨s, hs⟩ := hx₀R.1
    have hfix : (d : EscapingQuotient z) * x₀ * (d : EscapingQuotient z)⁻¹ = x₀ := by
      rw [← hs, ← sylowBar_sylowTorusAction hz hDN, show Φ d = 1 from hd]
      rfl
    obtain ⟨d₀, -, huniq⟩ := hlin.regular x₀ hx₀R hx₀1 x₀ hx₀R hx₀1
    have h1 := huniq d ⟨d.2, hfix⟩
    have h2 := huniq 1 ⟨D.one_mem, by group⟩
    exact Subgroup.mem_bot.mpr (Subtype.ext (h1.trans h2.symm))
  have hYodd : Odd (Nat.card Y) := by
    rw [hY, ← Subgroup.index_ker]
    have hle : (S : Subgroup G).subgroupOf (Subgroup.normalizer ((S : Subgroup G) : Set G)) ≤
        ((S : Subgroup G).normalizerMonoidHom).ker := by
      rw [Subgroup.normalizerMonoidHom_ker]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact Subgroup.mem_centralizer_iff.mpr fun s hs => hcomm s hs x hx
    have h1 := Subgroup.index_dvd_of_le hle
    have h2 : ((S : Subgroup G).subgroupOf (Subgroup.normalizer ((S : Subgroup G) : Set G))).index
        ∣ (S : Subgroup G).index := Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer
    have h3 : Odd (S : Subgroup G).index :=
      Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Sylow.not_dvd_index S))
    exact Odd.of_dvd_nat (Odd.of_dvd_nat h3 h2) h1
  have hYtrans : ∀ v w : (S : Subgroup G), v ≠ 1 → w ≠ 1 → ∃ y ∈ Y, y v = w := by
    intro v w hv hw
    obtain ⟨n, hn, hnvw⟩ := caseOne_sylow_transitive hset hz hesc hJ hzJ hlin v v.2 w w.2
      (fun h => hv (Subtype.ext h)) (fun h => hw (Subtype.ext h))
    refine ⟨(S : Subgroup G).normalizerMonoidHom ⟨n⁻¹, Subgroup.inv_mem _ hn⟩, ⟨_, rfl⟩,
      Subtype.ext ?_⟩
    change n⁻¹ * (v : G) * n⁻¹⁻¹ = w
    rw [inv_inv, hnvw]
  have hC₀Y : Φ.range ≤ Y := by
    rintro _ ⟨d, rfl⟩
    obtain ⟨m, hmN, hmd, hact⟩ := exists_normalizer_sylowBar_lift hz (hDN d.2)
    refine ⟨⟨m, hmN⟩, MulEquiv.ext fun s => sylowBar_injective hz ?_⟩
    rw [sylowBar_sylowTorusAction hz hDN, ← hact s ((Subgroup.mem_normalizer_iff.mp hmN s).mp s.2)]
    rfl
  have : IsCyclic D := hlin.torus_cyclic
  have hC₀cyc : IsCyclic Φ.range :=
    isCyclic_of_surjective Φ.rangeRestrict Φ.rangeRestrict_surjective
  have hC₀card : Nat.card Φ.range = q - 1 :=
    (Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv).symm.trans hlin.torus_card
  have hC₀z : ∀ c ∈ Φ.range, c ⟨z, hz.1⟩ = ⟨z, hz.1⟩ := by
    rintro _ ⟨d, rfl⟩
    apply sylowBar_injective hz
    rw [sylowBar_sylowTorusAction hz hDN, sylowBar_self, (hquot.commute_bar _).eq,
      mul_inv_cancel_right]
  have hC₀reg : ∀ w ∈ sylowComponentPreimage hz J, w ≠ 1 →
      ∀ w' ∈ sylowComponentPreimage hz J, w' ≠ 1 → ∃! c, c ∈ Φ.range ∧ c w = w' := by
    intro w hw hw1 w' hw' hw'1
    have hwR : sylowBar hz w ∈ (sylowBar hz).range ⊓ J := ⟨⟨w, rfl⟩, hw⟩
    have hw'R : sylowBar hz w' ∈ (sylowBar hz).range ⊓ J := ⟨⟨w', rfl⟩, hw'⟩
    have hwb1 : sylowBar hz w ≠ 1 := fun h => hw1 (sylowBar_injective hz (h.trans (map_one _).symm))
    have hw'b1 : sylowBar hz w' ≠ 1 := fun h =>
      hw'1 (sylowBar_injective hz (h.trans (map_one _).symm))
    obtain ⟨d, ⟨hd, hdw⟩, huniq⟩ := hlin.regular _ hwR hwb1 _ hw'R hw'b1
    refine ⟨Φ ⟨d, hd⟩, ⟨⟨_, rfl⟩, sylowBar_injective hz ?_⟩, ?_⟩
    · rw [sylowBar_sylowTorusAction hz hDN]
      exact hdw
    · rintro c ⟨⟨d', rfl⟩, hd'w⟩
      have h : (d' : EscapingQuotient z) = d := huniq d' ⟨d'.2, by
        rw [← sylowBar_sylowTorusAction hz hDN]
        exact congrArg (sylowBar hz) hd'w⟩
      rw [show d' = ⟨d, hd⟩ from Subtype.ext h]
  have hz1 : (⟨z, hz.1⟩ : (S : Subgroup G)) ≠ 1 := by
    intro h
    have h2 := hz.2.1
    rw [show z = 1 from congrArg Subtype.val h, orderOf_one] at h2
    exact absurd h2 (by decide)
  exact (card_eq_twentyOne_of_oddTransitive_mulAut hS2 hq hn hz1
    (isCompl_zpowers_sylowComponentPreimage hset hz hesc hJ hzJ hlin)
    (card_sylowComponentPreimage hz hlin) hYodd hYtrans hC₀Y hC₀cyc hC₀card hC₀z hC₀reg).1

end CFSG.ProperTwoGeneratedCore.Lemma37
