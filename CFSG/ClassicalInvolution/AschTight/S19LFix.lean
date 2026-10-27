module

public import CFSG.ClassicalInvolution.AschTight.S19LExact
public import CFSG.ClassicalInvolution.AschTight.S19QStmt
public import CFSG.ClassicalInvolution.AschTight.S1911P3e
public import CFSG.ClassicalInvolution.AschTight.S19MCenter
public import CFSG.ClassicalInvolution.AschTight.S19QAct

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19L

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q (secY secE secFam secK)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W : Subgroup G}

theorem map_le_fixingSubgroup (hd : Sec19Data p f K z S W) {a : G}
    (hO : oddCoreOf (secK K a) = ⊥) {H : Subgroup ↥(Subgroup.centralizer ({a} : Set G))}
    (hH : ∀ h ∈ H, (h : G) * z = z * (h : G) ∧ (h : G) ∈ centralizerModOdd ⊤ K) :
    H.map (S1911.secAct (secY K a)) ≤
      fixingSubgroup (MulAut (secE K a)) (secK K a : Set (secE K a)) := by
  rintro _ ⟨h, hh, rfl⟩
  rw [mem_fixingSubgroup_iff]
  intro x hx
  rw [MulAut.smul_def]
  exact S19Q.secAct_fixes_of_mem_cStar hd hO (hH h hh).1 (hH h hh).2 x hx

theorem false_of_mem_derived (hFG2 : S19Q.FactFG2) (hd : Sec19Data p f K z S W) {a : G}
    {e₁ : ℕ} (h5 : 5 ≤ p ^ e₁) (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hmem : IsClassicalMember p e₁ (S1911.perfectCoreIn K a) ⟨z, hzA⟩)
    (hΩ : HypOmegaMod p e₁ (S1911.conjFamily (S1911.perfectCoreIn K a)))
    (hDE : Disconnected.DEdgeless (S1911.conjFamily (S1911.perfectCoreIn K a))) {e₀ : ℕ}
    (hsec : SectionLieType p e₀ (S1911.conjFamily (S1911.perfectCoreIn K a))
        (S1911.conjGen (S1911.perfectCoreIn K a)) .PSL 3 ∨
      SectionLieType p e₀ (S1911.conjFamily (S1911.perfectCoreIn K a))
        (S1911.conjGen (S1911.perfectCoreIn K a)) .PSU 3)
    {H : Subgroup ↥(Subgroup.centralizer ({a} : Set G))}
    (hH : ∀ h ∈ H, (h : G) * z = z * (h : G) ∧ (h : G) ∈ centralizerModOdd ⊤ K)
    {y : ↥(Subgroup.centralizer ({a} : Set G))} (hy : y ∈ ⁅⁅H, H⁆, ⁅H, H⁆⁆)
    (hodd : Odd (orderOf ((⟨z, hzA⟩ : ↥(Subgroup.centralizer ({a} : Set G)))⁻¹ * y))) :
    False := by
  have hp2 : p ≠ 2 := hd.tight.branch.odd
  have := S1911.conjGen_normal (S1911.perfectCoreIn K a)
  have hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Subgroup.mem_subgroupOf.mp hmem.mem
  obtain ⟨tg, htg, hsecT⟩ : ∃ tg : CFSG.Assembly.LowTwoRank.StatedLieTag,
      (tg = .PSL ∨ tg = .PSU) ∧ SectionLieType p e₀ (S1911.conjFamily (S1911.perfectCoreIn K a))
        (S1911.conjGen (S1911.perfectCoreIn K a)) tg 3 := by
    rcases hsec with h | h
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩
  obtain ⟨D, hcard, i, hti, hki⟩ := hsecT
  have hconj := conjInvariant_oddQuotientFamily
    (S1911.inClass_restrict_conjugates hmem).conjInvariant
  have M := S1911.ih8Model_of_lieSystemData D hcard i hconj
  have htg' : D.tag i = .PSL ∨ D.tag i = .PSU := hti ▸ htg
  obtain ⟨hO, h5₀⟩ := secK_exact hd h5 hΩ hDE M htg'
  have hO2 := CFSG.ComponentClassification.OddCore.quotient_corefree
    ↥(S1911.conjGen (S1911.perfectCoreIn K a))
  have hu1 := S1911.isUniqueInvolution_secImg hd hzA hzKa 1
  have : Nontrivial (secE K a) := ⟨⟨_, 1, hu1.ne_one⟩⟩
  have htag6 : S1911.IsT6Tag (D.tag i) (D.rank i) := by
    rw [hki]
    rcases htg' with h | h <;> rw [h]
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  have hsimple := S1911.isSimpleGroup_of_lieSystemData S19M.factM3 hp2 D hcard i htag6 hO2
  have hcen : Subgroup.center (secE K a) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (secE K a)) with h | h
    · exact h
    · exfalso
      obtain ⟨x, -, w, -, hxw⟩ := S1911.exists_noncomm_secImg hd h5 hzA hmem
      exact hxw (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top w) x)
  have hKΦ : secK K a ∈ secFam K a :=
    (S1911.mem_secFamily_iff (S1911.perfectCoreIn K a) (secK K a)).mpr ⟨1, by rw [conjSub_one]⟩
  have hA := hFG2 p e₀ hp2 h5₀ (secE K a) (secFam K a) (D.tag i) (D.rank i) (D.exp i)
    (by rw [hki]; exact htg'.imp (⟨·, rfl⟩) (⟨·, rfl⟩)) ⟨M⟩ (secK K a) hKΦ
  have hHA := map_le_fixingSubgroup hd hO hH
  have hy1 : S1911.secAct (secY K a) y = 1 := by
    have h1 : (⁅⁅H, H⁆, ⁅H, H⁆⁆).map (S1911.secAct (secY K a)) ≤ ⊥ := by
      rw [Subgroup.map_commutator, Subgroup.map_commutator, ← hA]
      exact Subgroup.commutator_mono (Subgroup.commutator_mono hHA hHA)
        (Subgroup.commutator_mono hHA hHA)
    exact Subgroup.mem_bot.mp (h1 ⟨y, hy, rfl⟩)
  set zA : ↥(Subgroup.centralizer ({a} : Set G)) := ⟨z, hzA⟩ with hzA'
  set o := zA⁻¹ * y with ho
  have hφz : S1911.secAct (secY K a) zA = (S1911.secAct (secY K a) o)⁻¹ := by
    have e : y = zA * o := by rw [ho]; group
    rw [e, map_mul] at hy1
    exact eq_inv_of_mul_eq_one_left hy1
  have hz2 : S1911.secAct (secY K a) zA ^ 2 = 1 := by
    have hzz : zA ^ 2 = 1 := by rw [← hmem.orderOf_eq_two]; exact pow_orderOf_eq_one zA
    rw [← map_pow, hzz, map_one]
  have hzo : S1911.secAct (secY K a) zA ^ orderOf o = 1 := by
    rw [hφz, inv_pow, ← map_pow, pow_orderOf_eq_one, map_one, inv_one]
  have hz1 : S1911.secAct (secY K a) zA = 1 := by
    have h2 := orderOf_dvd_of_pow_eq_one hz2
    have h3 := orderOf_dvd_of_pow_eq_one hzo
    have h4 : orderOf (S1911.secAct (secY K a) zA) ∣ Nat.gcd 2 (orderOf o) := Nat.dvd_gcd h2 h3
    rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hodd)] at h4
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4)
  have hzY : zA ∈ secY K a := S1911.le_conjGen ⟨1, conjSub_one _⟩ hzKa
  rw [S1911.secAct_of_mem _ hzY] at hz1
  have hzc : (QuotientGroup.mk (⟨zA, hzY⟩ : ↥(secY K a)) : secE K a) ∈
      Subgroup.center (secE K a) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut (secE K a) => φ g) hz1
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * _ = _ * g * _⁻¹ * _ := by rw [this]
      _ = _ := by group
  rw [hcen, Subgroup.mem_bot] at hzc
  apply hu1.ne_one
  rw [← hzc]
  show QuotientGroup.mk' _ _ = QuotientGroup.mk' _ _
  congr 1
  exact Subtype.ext (by simp [hzA'])

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19L
