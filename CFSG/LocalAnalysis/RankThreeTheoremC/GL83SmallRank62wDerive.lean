module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yCommon
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wInvert
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wSylow
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zGlue
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem sr630c_mem_normalizer_centralizer {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) : g ∈ normalizer (centralizer (H : Set G) : Set G) := by
  have key : ∀ g ∈ normalizer (H : Set G), ∀ c ∈ centralizer (H : Set G),
      g * c * g⁻¹ ∈ centralizer (H : Set G) := by
    intro g hg c hc
    rw [mem_centralizer_iff]
    intro h hh
    have hh' : g⁻¹ * h * g ∈ H := by
      have := (mem_normalizer_iff.mp (inv_mem hg) h).mp hh
      simpa using this
    have hc' : g⁻¹ * h * g * c = c * (g⁻¹ * h * g) := mem_centralizer_iff.mp hc _ hh'
    calc h * (g * c * g⁻¹) = g * (g⁻¹ * h * g * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * h * g)) * g⁻¹ := by rw [hc']
      _ = g * c * g⁻¹ * h := by group
  rw [mem_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun hc => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hc
  simpa [mul_assoc] using this

theorem lemma630_concl_of_core (hS : Setting G) (hK : KFactZAction629)
    {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G} {T : Subgroup G} {f : ℕ}
    (h614 : ∀ S₀ : Subgroup G, S₀ ≤ smallRankS x T → S₀ ≠ ⊥ →
      zpowers z ≤ normalizer (S₀ : Set G) → normalizer (S₀ : Set G) ≤ M)
    (hyp : Lemma630Hyp G p P M x z T f) {E : Subgroup G} (hE : SmallRankSBSylow p f x z T E)
    (hEM : E ⊓ M = ⊥) (hiii : Lemma630Iii p f x) : Lemma630Concl p x z T f := by
  obtain ⟨hf, hcov, h28, hfp, hf2, hfD, h29⟩ := hyp
  have hp : p.Prime := hf.prime
  have hp2 : p ≠ 2 := hf.ne_two
  have : Fact f.Prime := ⟨hfp⟩
  have hfp' : f ≠ p := sr629_ne_prime hp hfp x hfD
  have hlr3 : rankThreeLocalRank f G ≤ 3 := smallRank_localRank_le_three hS hfp hf2
  have hlr2 : p = 3 → rankThreeLocalRank f G ≤ 2 := by
    intro hp3
    subst hp3
    exact localRank_le_two_of_three hS hf.situation hfp (sr629_five_le hfp hf2 hfp')
  have hH6 : ¬ (p = 3 ∧ ∃ n : ℕ, rankThreeIsQ8CentralCyclic (smallRankS x T) n) := by
    rintro ⟨hp3, n, hn⟩
    subst hp3
    exact hf.fails ⟨rfl, Or.inr ⟨⟨n, hn⟩, hcov⟩⟩
  obtain ⟨hp35, hQ, hQ8, hfit⟩ := h28
  obtain ⟨⟨hi5, hi3, hcen⟩, -, -, hFe, hF4, hFinv⟩ := h29
  have hEC : E ≤ centralizer (smallRankF p f x : Set G) := hE.1
  have hEp : IsPGroup f E := hE.2.1
  have hEs : ¬ f ∣ (E.subgroupOf (centralizer (smallRankF p f x : Set G))).index := hE.2.2.1
  have hSE : smallRankS x T ≤ normalizer (E : Set G) := le_sup_left.trans hE.2.2.2
  have hBE : zpowers x ⊔ zpowers z ≤ normalizer (E : Set G) := le_sup_right.trans hE.2.2.2
  have hzE : zpowers z ≤ normalizer (E : Set G) := le_sup_right.trans hBE
  have hFne : smallRankF p f x ≠ ⊥ := by
    intro hF
    have h1 : Nat.card (smallRankF p f x) = 1 := by rw [hF]; exact Subgroup.card_bot
    rw [hF4] at h1
    exact (Nat.one_lt_pow (by norm_num) hfp.one_lt).ne' h1
  have hFE : smallRankF p f x ≤ E :=
    k631_le_of_sylow_centralizer hfp (sr629_F_isPGroup hfp x) hFe.1 hEC hEp hEs
  have hFM : smallRankF p f x ⊓ M = ⊥ := by
    rw [eq_bot_iff, ← hfit]
    exact inf_le_inf_right M (sr629_F_le_fitting hp hfp hf2 x)
  have hzx : z ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hf.central.centralizes x hf.point.mem).symm
  have hzF : z ∈ normalizer (smallRankF p f x : Set G) := sr629_centralizer_le_normalizer_F hp x hzx
  have hzS : zpowers z ≤ normalizer (smallRankS x T : Set G) := hf.z_le_normalizer_S
  have hSCF : smallRankS x T ⊓ centralizer (smallRankF p f x : Set G) = ⊥ := by
    by_contra hne
    have hz0 : zpowers z ≤ normalizer
        ((smallRankS x T ⊓ centralizer (smallRankF p f x : Set G) : Subgroup G) : Set G) := by
      rw [zpowers_le]
      exact inf_normalizer_le_normalizer_inf
        ⟨hzS (mem_zpowers z), sr630c_mem_normalizer_centralizer hzF⟩
    have hN := h614 _ inf_le_left hne hz0
    have hFC : smallRankF p f x ≤ centralizer
        ((smallRankS x T ⊓ centralizer (smallRankF p f x : Set G) : Subgroup G) : Set G) := by
      intro a ha
      rw [mem_centralizer_iff]
      intro s hs
      exact (mem_centralizer_iff.mp hs.2 a ha).symm
    refine hFne (eq_bot_iff.mpr ?_)
    calc smallRankF p f x ≤ smallRankF p f x ⊓ M :=
          le_inf le_rfl (hFC.trans ((centralizer_le_normalizer _).trans hN))
      _ = ⊥ := hFM
      _ ≤ ⊥ := le_rfl
  obtain ⟨-, y, -, -, -, hyZ, -, hy2, hy1, -, -⟩ : ∃ t y g : G,
      t ∈ smallRankS x T ∧ g ∈ smallRankS x T ∧ y ∈ smallRankCenter (smallRankS x T) ∧
      t ^ 2 = 1 ∧ y ^ 2 = 1 ∧ y ≠ 1 ∧ t * y = y * t ∧ g * t * g⁻¹ = t * y := by
    rcases hp35 with hp3 | hp5
    · obtain ⟨n, hn⟩ := hi3 hp3
      exact k631_tyg_quaternion hn
    · obtain ⟨n, hn⟩ := hi5 hp5
      exact k631_tyg_dihedral hn
  have hyZ0 : y ∈ smallRankOmega 2 (smallRankCenter (smallRankS x T)) :=
    Subgroup.subset_closure ⟨hyZ, hy2⟩
  have hZ0S : smallRankOmega 2 (smallRankCenter (smallRankS x T)) ≤ smallRankS x T :=
    sr629_omega_center_le 2 _
  have hyS : y ∈ smallRankS x T := hZ0S hyZ0
  have hyy : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hy2)
  have hyinv : ∀ a ∈ smallRankF p f x, y * a * y⁻¹ = a⁻¹ :=
    hFinv y (by rw [hcen]; exact hyZ0) hy1
  have hZ0 : ∀ s ∈ smallRankOmega 2 (smallRankCenter (smallRankS x T)), s = 1 ∨ s = y := by
    intro s hs
    by_cases hs1 : s = 1
    · exact Or.inl hs1
    right
    have hsinv := hFinv s (by rw [hcen]; exact hs) hs1
    have hsyC : s * y ∈ smallRankS x T ⊓ centralizer (smallRankF p f x : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem (hZ0S hs) hyS, ?_⟩
      rw [mem_centralizer_iff]
      intro a ha
      have h3 : s * y * a * (s * y)⁻¹ = a := by
        calc s * y * a * (s * y)⁻¹ = s * (y * a * y⁻¹) * s⁻¹ := by group
          _ = s * a⁻¹ * s⁻¹ := by rw [hyinv a ha]
          _ = a⁻¹⁻¹ := hsinv a⁻¹ (inv_mem ha)
          _ = a := inv_inv a
      exact (mul_inv_eq_iff_eq_mul.mp h3).symm
    rw [hSCF, Subgroup.mem_bot] at hsyC
    rw [eq_inv_of_mul_eq_one_left hsyC, hyy]
  have hZ0ne : smallRankOmega 2 (smallRankCenter (smallRankS x T)) ≠ ⊥ := by
    intro h
    rw [h] at hyZ0
    exact hy1 (Subgroup.mem_bot.mp hyZ0)
  have hzZ0 : zpowers z ≤
      normalizer (smallRankOmega 2 (smallRankCenter (smallRankS x T)) : Set G) := by
    rw [zpowers_le]
    exact sr629_mem_normalizer_smallRankOmega 2
      (sr629_mem_normalizer_smallRankCenter (hzS (mem_zpowers z)))
  have hNZ0 := h614 _ hZ0S hZ0ne hzZ0
  have hCy : centralizer ({y} : Set G) ≤ M := by
    intro g hg
    refine hNZ0 (centralizer_le_normalizer _ ?_)
    rw [mem_centralizer_iff]
    intro s hs
    rcases hZ0 s hs with rfl | rfl
    · rw [one_mul, mul_one]
    · exact (mem_centralizer_singleton_iff.mp hg).symm
  have hfix : ∀ e ∈ E, y * e = e * y → e = 1 := by
    intro e he hye
    have hem : e ∈ E ⊓ M := ⟨he, hCy (mem_centralizer_singleton_iff.mpr hye.symm)⟩
    rw [hEM] at hem
    exact Subgroup.mem_bot.mp hem
  have hEc : IsMulCommutative E :=
    sr630a_isMulCommutative_of_conj_eq_inv (sr630a_conj_eq_inv hy2 (hSE hyS) hfix)
  have hEcen : ∀ e ∈ E, e ∈ smallRankCenter E := by
    intro e he
    refine Subgroup.mem_inf.mpr ⟨he, ?_⟩
    rw [mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (hEc.is_comm.comm ⟨h, hh⟩ ⟨e, he⟩)
  have hE₁e : IsElemAbelian f (smallRankOmega f (smallRankCenter E)) :=
    sr629_isElemAbelian_omega_center f E
  have hE₁E : smallRankOmega f (smallRankCenter E) ≤ E := sr629_omega_center_le f E
  have hall : ∀ e ∈ E, e ^ f = 1 → e ∈ smallRankOmega f (smallRankCenter E) :=
    fun e he hef => Subgroup.subset_closure ⟨hEcen e he, hef⟩
  have hFE₁ : smallRankF p f x ≤ smallRankOmega f (smallRankCenter E) :=
    fun a ha => hall a (hFE ha) (hFe.2 a ha)
  have hE₁ne : smallRankOmega f (smallRankCenter E) ≠ ⊥ := by
    intro h
    apply hFne
    rw [eq_bot_iff, ← h]
    exact hFE₁
  have hNE₁ : ∀ g ∈ normalizer (E : Set G),
      g ∈ normalizer (smallRankOmega f (smallRankCenter E) : Set G) := fun g hg =>
    sr629_mem_normalizer_smallRankOmega f (sr629_mem_normalizer_smallRankCenter hg)
  have hSzE₁ : smallRankS x T ⊔ zpowers z ≤
      normalizer (smallRankOmega f (smallRankCenter E) : Set G) :=
    sup_le (fun s hs => hNE₁ s (hSE hs)) (fun g hg => hNE₁ g (hzE hg))
  have hH2 : ∀ S₀ : Subgroup G, S₀ ≤ smallRankS x T → S₀ ≠ ⊥ →
      zpowers z ≤ normalizer (S₀ : Set G) →
      smallRankOmega f (smallRankCenter E) ⊓ centralizer (S₀ : Set G) = ⊥ := by
    intro S₀ hS₀S hS₀1 hzS₀
    rw [eq_bot_iff, ← hEM]
    exact inf_le_inf hE₁E ((centralizer_le_normalizer _).trans (h614 S₀ hS₀S hS₀1 hzS₀))
  have hH3 : smallRankOmega f (smallRankCenter E) ⊓ centralizer ({z} : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hEM]
    exact inf_le_inf hE₁E
      ((sr628_centralizer_le_normalizer_zpowers z).trans (hf.normalizer_zpowers_le hS))
  obtain ⟨⟨hcard, -⟩, -, -⟩ :=
    hK G p f hp hfp hp2 hf2 hfp' hp35 (smallRankS x T) (smallRankOmega f (smallRankCenter E)) z
      hf.S_isPGroup hE₁e hE₁ne hf.central.pow_eq_one hf.central.ne_one hzS hSzE₁ hQ hQ8 hH2 hH3
      (smallRankInvolutionRankLE_of_localRank hfp _ _ hlr3)
      (fun hp3 => smallRankInvolutionRankLE_of_localRank hfp _ _ (hlr2 hp3)) hH6
  have hE₁F : smallRankOmega f (smallRankCenter E) = smallRankF p f x :=
    (Subgroup.eq_of_le_of_card_ge hFE₁ (by rw [hcard, hF4])).symm
  have hFall : ∀ e ∈ E, e ^ f = 1 → e ∈ smallRankF p f x := fun e he hef =>
    hE₁F ▸ hall e he hef
  exact ⟨⟨E, hEC, hEp, hEs, hE.2.2.2, hEc, sr630a_pRank_eq hfp hFE hFe hF4 hFall,
    sr630a_not_dvd_index hfp hf2 hFE hFne hFe.2 hFall hEp hEC hEs hiii⟩, hiii⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
