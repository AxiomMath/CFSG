module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Choice
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Helpers
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.LayerLemma
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt6
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt69

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Prelim

variable {G : Type} [Group G] [Finite G]

theorem exists_prime_ne_of_twoPrimes {X : Subgroup G} (hX : TwoPrimes X) (r : ℕ) :
    ∃ b : ℕ, b ∈ piOf X ∧ b ≠ r := by
  have hfin : (piOf X).Finite := by
    refine (Set.finite_Iic (Nat.card ↥X)).subset ?_
    intro s hs
    exact Nat.le_of_dvd Nat.card_pos hs.2
  have h1 : 1 < (piOf X).ncard := hX
  obtain ⟨a, ha, c, hc, hac⟩ := (Set.one_lt_ncard hfin).mp h1
  by_cases har : a = r
  · exact ⟨c, hc, fun h => hac (har.trans h.symm)⟩
  · exact ⟨a, ha, har⟩

theorem Ep_ne_bot {M : Subgroup G} {r b : ℕ} (hr : r.Prime) (hb : b.Prime) (hbr : b ≠ r)
    (hdvd : b ∣ Nat.card ↥(Fm M)) : Ep r M ≠ ⊥ := by
  have : Fact b.Prime := ⟨hb⟩
  obtain ⟨Q⟩ : Nonempty (Sylow b ↥(Fm M)) := inferInstance
  have hQn : (Q : Subgroup ↥(Fm M)).Normal := Group.IsNilpotent.sylow_normal (Fm_nilpotent M) b Q
  have hQne : (Q : Subgroup ↥(Fm M)) ≠ ⊥ := Sylow.ne_bot_of_dvd_card Q hdvd
  have hcop : Nat.Coprime r (Nat.card ↥(Q : Subgroup ↥(Fm M))) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp Q.isPGroup'
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hr hb).mpr (Ne.symm hbr))
  have hQle : (Q : Subgroup ↥(Fm M)) ≤ pPrimeCore r ↥(Fm M) := le_sSup ⟨hQn, hcop⟩
  intro hbot
  have h0 : pPrimeCore r ↥(Fm M) = ⊥ := by
    have : pPrimeCoreOf r (Fm M) = ⊥ := hbot
    unfold pPrimeCoreOf at this
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Fm M).subtype_injective).mp this
  exact hQne (le_bot_iff.mp (h0 ▸ hQle))

omit [Finite G] in
theorem le_normalizer_zOf {H E : Subgroup G} (hH : H ≤ normalizer (E : Set G)) :
    H ≤ normalizer ((zOf E : Subgroup G) : Set G) := by
  have key : ∀ h ∈ H, ∀ x ∈ zOf E, h * x * h⁻¹ ∈ zOf E := by
    intro h hh x hx
    have hxE : x ∈ E := hx.1
    have hxc : x ∈ centralizer (E : Set G) := hx.2
    refine ⟨(mem_normalizer_iff.mp (hH hh) x).mp hxE, ?_⟩
    show h * x * h⁻¹ ∈ centralizer (E : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have he' : h⁻¹ * e * h ∈ E := by
      have := (mem_normalizer_iff.mp (hH (inv_mem hh)) e).mp he
      simpa using this
    have := Subgroup.mem_centralizer_iff.mp hxc _ he'
    calc e * (h * x * h⁻¹) = h * ((h⁻¹ * e * h) * x) * h⁻¹ := by group
      _ = h * (x * (h⁻¹ * e * h)) * h⁻¹ := by rw [this]
      _ = h * x * h⁻¹ * e := by group
  intro h hh
  rw [mem_normalizer_iff]
  intro x
  exact ⟨fun hx => key h hh x hx, fun hx => by
    have := key h⁻¹ (inv_mem hh) _ hx
    simpa [mul_assoc] using this⟩

theorem normalizer_eq_of_normalized {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ} (hC : Ctx6 G z k S M p)
    {B : Subgroup G} (hB : B ≠ ⊥) (hBM : B ≤ M) (hn : M ≤ normalizer (B : Set G)) :
    normalizer (B : Set G) = M := by
  refine le_antisymm ?_ hn
  by_contra hnle
  have hne : M ≠ normalizer (B : Set G) := fun h => hnle (h ▸ le_rfl)
  have hlt : M < normalizer (B : Set G) := lt_of_le_of_ne hn hne
  have htop : normalizer (B : Set G) = ⊤ := hC.coatom.2 _ hlt
  have hBn : B.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have hsimple : IsSimpleGroup G := hC.ctx.std.kps.1
  rcases (haveI := hBn; hsimple.eq_bot_or_eq_top_of_normal B) with h | h
  · exact hB h
  · have : (⊤ : Subgroup G) ≤ M := h ▸ hBM
    exact hC.coatom.1 (top_le_iff.mp this)

theorem normalizer_ne_top {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ} (hC : Ctx6 G z k S M p)
    {X : Subgroup G} (hX : X ≠ ⊥) (hXM : X ≤ M) : normalizer (X : Set G) ≠ ⊤ := by
  intro htop
  have hXn : X.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have hsimple : IsSimpleGroup G := hC.ctx.std.kps.1
  rcases (haveI := hXn; hsimple.eq_bot_or_eq_top_of_normal X) with h | h
  · exact hX h
  · have : (⊤ : Subgroup G) ≤ M := h ▸ hXM
    exact hC.coatom.1 (top_le_iff.mp this)

end Prelim

section Cor

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_le_left_of_normalizes {X Y : Subgroup G} (hY : Y ≤ normalizer (X : Set G)) : ⁅X, Y⁆ ≤ X := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have h1 : y * x⁻¹ * y⁻¹ ∈ X := (mem_normalizer_iff.mp (hY hy) x⁻¹).mp (X.inv_mem hx)
  have : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by simp [commutatorElement_def, mul_assoc]
  rw [this]
  exact X.mul_mem hx h1

omit [Finite G] in
theorem conj_mem_commutator {P Y : Subgroup G} {c : G} (hP : c ∈ normalizer (P : Set G))
    (hY : ∀ y ∈ Y, c * y * c⁻¹ = y) : ∀ x ∈ ⁅P, Y⁆, c * x * c⁻¹ ∈ ⁅P, Y⁆ := by
  intro x hx
  rw [Subgroup.commutator_def] at hx ⊢
  refine Subgroup.closure_induction (p := fun x _ => c * x * c⁻¹ ∈ Subgroup.closure
    {g | ∃ g₁ ∈ P, ∃ g₂ ∈ Y, ⁅g₁, g₂⁆ = g}) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨g₁, hg₁, g₂, hg₂, rfl⟩
    refine Subgroup.subset_closure ⟨c * g₁ * c⁻¹, (mem_normalizer_iff.mp hP g₁).mp hg₁, g₂, hg₂, ?_⟩
    have h' := map_commutatorElement (MulAut.conj c) g₁ g₂
    have h2 := hY g₂ hg₂
    simp only [MulAut.conj_apply, h2] at h'
    exact h'.symm
  · simp
  · intro a b _ _ ha hb
    have : c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ha hb
  · intro a _ ha
    have : c * a⁻¹ * c⁻¹ = (c * a * c⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ha

omit [Finite G] in
theorem le_normalizer_commutator_zpowers {P : Subgroup G} {z c : G} (hP : c ∈ normalizer (P : Set G))
    (hz : c ∈ Cen z) : c ∈ normalizer ((⁅P, zpowers z⁆ : Subgroup G) : Set G) := by
  have hcz : c * z * c⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hz
    rw [this]; group
  have hY : ∀ y ∈ zpowers z, c * y * c⁻¹ = y := by
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hcz]
  have hY' : ∀ y ∈ zpowers z, c⁻¹ * y * c⁻¹⁻¹ = y := by
    intro y hy
    have := hY y hy
    calc c⁻¹ * y * c⁻¹⁻¹ = c⁻¹ * (c * y * c⁻¹) * c := by rw [this]; simp
      _ = y := by group
  rw [mem_normalizer_iff]
  intro x
  exact ⟨fun hx => conj_mem_commutator hP hY x hx, fun hx => by
    have := conj_mem_commutator (inv_mem hP) hY' _ hx
    simpa [mul_assoc] using this⟩

theorem prop6_5_of (h62 : Prop6_2) : Prop6_5 := by
  intro G _ _ z k S M p hC A r hr hAc hAr hAN X hXE hX0 hXz
  have hFM : Fm M ≤ M := Fm_le M
  obtain ⟨b, hb, hbr⟩ := exists_prime_ne_of_twoPrimes hC.twoPrimes r
  have hE0 : Ep r M ≠ ⊥ := Ep_ne_bot hr hb.1 hbr hb.2
  have hB0 : zOf (Ep r M) ≠ ⊥ := by
    have hnil : Group.IsNilpotent ↥(Ep r M) := by
      have : Group.IsNilpotent ↥((Ep r M).subgroupOf (Fm M)) := by
        have := Fm_nilpotent M
        infer_instance
      exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (Ep_le_Fm r M))
    have hne : (⊤ : Subgroup ↥(Ep r M)) ≠ ⊥ := by
      have : Nontrivial ↥(Ep r M) := (Subgroup.nontrivial_iff_ne_bot _).mpr hE0
      obtain ⟨x, hx⟩ := exists_ne (1 : ↥(Ep r M))
      intro h
      exact hx ((Subgroup.mem_bot).mp (h ▸ Subgroup.mem_top x))
    have hz := Group.IsNilpotent.inf_center_ne_bot_of_normal (G := ↥(Ep r M)) (H := ⊤) hne
    obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hz
    intro hbot
    apply ha
    have haE : ((a : ↥(Ep r M)) : G) ∈ zOf (Ep r M) := by
      refine ⟨(a : ↥(Ep r M)).2, ?_⟩
      show ((a : ↥(Ep r M)) : G) ∈ centralizer ((Ep r M : Subgroup G) : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := Subgroup.mem_center_iff.mp a.2.2 ⟨y, hy⟩
      exact congrArg Subtype.val this
    rw [hbot, Subgroup.mem_bot] at haE
    exact Subtype.ext (Subtype.ext haE)
  have hBE : zOf (Ep r M) ≤ Ep r M := inf_le_left
  have hBM : zOf (Ep r M) ≤ M := hBE.trans ((Ep_le_Fm r M).trans hFM)
  have hBn : M ≤ normalizer ((zOf (Ep r M) : Subgroup G) : Set G) := le_normalizer_zOf (le_normalizer_Ep r M)
  have hBnorm : normalizer ((zOf (Ep r M) : Subgroup G) : Set G) = M := normalizer_eq_of_normalized hC hB0 hBM hBn
  have hBF : NF z M (zOf (Ep r M)) :=
    ⟨hBE.trans (Ep_le_Fm r M), hB0, hBn hC.z_mem, hBnorm.le⟩
  have hXFm : X ≤ Fm M := hXE.trans (Ep_le_Fm r M)
  have hXn : normalizer (X : Set G) ≠ ⊤ := normalizer_ne_top hC hX0 (hXFm.trans hFM)
  obtain ⟨N, hN, hXN⟩ : ∃ N : Subgroup G, IsCoatom N ∧ normalizer (X : Set G) ≤ N := by
    rcases eq_top_or_exists_le_coatom (normalizer (X : Set G)) with h | h
    · exact absurd h hXn
    · exact h
  have hOcX : Op r M ≤ centralizer (X : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (commute_Op_Ep r hr M)).trans
      (Subgroup.centralizer_le (fun x hx => hXE hx))
  have hBcX : zOf (Ep r M) ≤ centralizer (X : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le (fun x hx => hXE hx))
  have hcN : centralizer (X : Set G) ≤ N := (Subgroup.centralizer_le_normalizer _).trans hXN
  have hH : Hyp62 z M N A (zOf (Ep r M)) r :=
    ⟨hN, hXN hXz, hr, (hAr.trans hOcX).trans hcN, hBcX.trans hcN, hAc, hAr, hAN, hBE, hBF⟩
  obtain ⟨-, -, hc⟩ := h62 G z k S M p hC N A (zOf (Ep r M)) r hH
  have hMN : Links M N := ⟨X, hXFm, inf_le_right.trans hXN⟩
  have hMeq : M = N := hc hMN
  exact ⟨hXFm, hX0, hXz, hMeq ▸ hXN⟩

theorem prop6_6_of (h61 : Prop6_1) (h65 : Prop6_5) : Prop6_6 := by
  intro G _ _ z k S M p hC X hXE hX0 hXz
  have hp := hC.prime
  have hzP : z ∈ normalizer ((Op p M : Subgroup G) : Set G) := le_normalizer_Op p M hC.z_mem
  have hAP : ⁅Op p M, zpowers z⁆ ≤ Op p M :=
    commutator_le_left_of_normalizes (Subgroup.zpowers_le.mpr hzP)
  have hA0 : ⁅Op p M, zpowers z⁆ ≠ ⊥ := by
    intro h
    apply hC.not_cen
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    exact this.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers z)))
  have hAC : Cen z ≤ normalizer ((⁅Op p M, zpowers z⁆ : Subgroup G) : Set G) := fun c hc =>
    le_normalizer_commutator_zpowers (le_normalizer_Op p M (hC.cen_le hc)) hc
  have hAz : z ∈ normalizer ((⁅Op p M, zpowers z⁆ : Subgroup G) : Set G) := hAC (mem_Cen_self z)
  have hAc : ⁅⁅Op p M, zpowers z⁆, zpowers z⁆ = ⁅Op p M, zpowers z⁆ :=
    commutator_zpowers_idem (A := Op p M) hC.orderOf_z hp hC.p_ne_two (isPGroup_Op p hp M) hzP
  have hAN : NF z M ⁅Op p M, zpowers z⁆ := h61 G z k S M p hC _ hAP hA0 hAC
  exact h65 G z k S M p hC _ p hp hAc hAP hAN X hXE hX0 hXz

theorem lemma6_10_of (h62 : Prop6_2) (h66 : Prop6_6) : Lemma6_10 := by
  intro G _ _ z k S M p hC Y Y₁ hYP hY0 hYz hYn hY₁ hY₁0 hY₁c hY₁N
  apply hYn
  have hp := hC.prime
  have hYFm : Y ≤ Fm M := hYP.trans (Op_le_Fm p hp M)
  have hYn_top : normalizer (Y : Set G) ≠ ⊤ := normalizer_ne_top hC hY0 (hYFm.trans (Fm_le M))
  obtain ⟨N, hN, hYN⟩ : ∃ N : Subgroup G, IsCoatom N ∧ normalizer (Y : Set G) ≤ N := by
    rcases eq_top_or_exists_le_coatom (normalizer (Y : Set G)) with h | h
    · exact absurd h hYn_top
    · exact h
  obtain ⟨b, hb, hbp⟩ := exists_prime_ne_of_twoPrimes hC.twoPrimes p
  have hE0 : Ep p M ≠ ⊥ := Ep_ne_bot hp hb.1 hbp hb.2
  have hEF : NF z M (Ep p M) := h66 G z k S M p hC (Ep p M) le_rfl hE0 (le_normalizer_Ep p M hC.z_mem)
  have hEcY : Ep p M ≤ centralizer (Y : Set G) := by
    have h1 : Op p M ≤ centralizer ((Ep p M : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (commute_Op_Ep p hp M)
    exact (Subgroup.le_centralizer_iff.mpr h1).trans (Subgroup.centralizer_le (fun y hy => hYP hy))
  have hcN : centralizer (Y : Set G) ≤ N := (Subgroup.centralizer_le_normalizer _).trans hYN
  have hH : Hyp62 z M N Y₁ (Ep p M) p :=
    ⟨hN, hYN hYz, hp, (hY₁.trans inf_le_right).trans hYN, hEcY.trans hcN, hY₁c, hY₁.trans inf_le_left,
      hY₁N, le_rfl, hEF⟩
  obtain ⟨-, -, hc⟩ := h62 G z k S M p hC N Y₁ (Ep p M) p hH
  have hMN : Links M N := ⟨Y, hYFm, inf_le_right.trans hYN⟩
  exact ⟨hYFm, hY0, hYz, (hc hMN) ▸ hYN⟩

end Cor

end CFSG.GH74.GLS.Stage2.Bender.Thm1
