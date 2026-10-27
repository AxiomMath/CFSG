module

public import CFSG.ClassicalInvolution.Phan.PhanDn.PointGraph
import all CFSG.ClassicalInvolution.Phan.PhanDn.Perp
import all CFSG.ClassicalInvolution.Phan.PhanDn.FlipSpace

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.BorelTits
open CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

@[expose] def IsSolid (σ : K ≃+* K) (M : Submodule K (Fin n ⊕ Fin n → K)) : Prop :=
  IsFlipflopSub σ M ∧ Module.finrank K M = n

theorem IsSolid.isLagrangian {M : Submodule K (Fin n ⊕ Fin n → K)} (hM : IsSolid σ M) :
    (quadPlusForm n K).IsLagrangian M := by
  refine ⟨(qSing_iff_isTotallySingular M).mp hM.1.total, ?_⟩
  rw [hM.2, finrank_flipSpace]

theorem flipOrth_eq_dFlipSub_of_isLagrangian (hσ : ∀ x, σ (σ x) = x)
    {M : Submodule K (Fin n ⊕ Fin n → K)} (hM : (quadPlusForm n K).IsLagrangian M) :
    flipOrth σ M = dFlipSub σ M := by
  rw [flipOrth_eq_qPerp_dFlipSub hσ, qPerp_dFlipSub hσ, qPerp_eq_of_isLagrangian hM]

private theorem polar_eq_zero_of_mem_qSing {W : Submodule K (Fin n ⊕ Fin n → K)}
    (hW : QSing W) {u v : Fin n ⊕ Fin n → K} (hu : u ∈ W) (hv : v ∈ W) :
    polar (quadPlus n K) u v = 0 := by
  have h := (mem_qPerp.mp (QSing.le_qPerp hW hu)) v hv
  rwa [polar_comm] at h

private theorem isLagrangian_dFlipSub (hσ : ∀ x, σ (σ x) = x)
    {M : Submodule K (Fin n ⊕ Fin n → K)} (hM : (quadPlusForm n K).IsLagrangian M) :
    (quadPlusForm n K).IsLagrangian (dFlipSub σ M) := by
  refine ⟨(qSing_iff_isTotallySingular _).mp (QSing.dFlipSub ?_), ?_⟩
  · exact (qSing_iff_isTotallySingular M).mpr hM.1
  · rw [finrank_dFlipSub hσ]
    exact hM.2

theorem even_finrank_inf_dFlipSub (hσ : ∀ x, σ (σ x) = x)
    {M : Submodule K (Fin n ⊕ Fin n → K)} (hM : (quadPlusForm n K).IsLagrangian M) :
    Even (Module.finrank K ↥(M ⊓ dFlipSub σ M)) := by
  have hn : Module.finrank K (Fin n ⊕ Fin n → K) = 2 * n := finrank_flipSpace n K
  have hE : (quadPlusForm n K).IsLagrangian (stdLag n K) := isLagrangian_stdLag n K
  have hMd : (quadPlusForm n K).IsLagrangian (dFlipSub σ M) := isLagrangian_dFlipSub hσ hM
  have hEd : (quadPlusForm n K).IsLagrangian (dFlipSub σ (stdLag n K)) :=
    isLagrangian_dFlipSub hσ hE
  have hp1 := QuadForm.IsLagrangian.even_add_add (Φ := quadPlusForm n K) (n := n) hn hM hMd hE
  have hp2 := QuadForm.IsLagrangian.even_add_add (Φ := quadPlusForm n K) (n := n) hn hM hE hEd
  have hmid : Module.finrank K ↥(dFlipSub σ M ⊓ stdLag n K) =
      Module.finrank K ↥(M ⊓ dFlipSub σ (stdLag n K)) := by
    have hEq : dFlipSub σ M ⊓ stdLag n K =
        dFlipSub σ (M ⊓ dFlipSub σ (stdLag n K)) := by
      rw [dFlipSub_inf hσ, dFlipSub_dFlipSub hσ]
    rw [hEq, finrank_dFlipSub hσ]
  have hzero : Module.finrank K ↥(stdLag n K ⊓ dFlipSub σ (stdLag n K)) = 0 := by
    rw [stdLag_inf_dFlipSub hσ, finrank_bot]
  rw [hmid] at hp1
  rw [hzero, Nat.sub_zero] at hp2
  rw [Nat.even_iff] at hp1 hp2 ⊢
  have hA : Module.finrank K ↥(M ⊓ dFlipSub σ M) ≤ n := by
    have h1 := Submodule.finrank_mono (inf_le_left : M ⊓ dFlipSub σ M ≤ M)
    have h2 := hM.2
    rw [hn] at h2
    omega
  omega

theorem IsFlipflopSub.sup_dFlipSub (hσ : ∀ x, σ (σ x) = x)
    {Y : Submodule K (Fin n ⊕ Fin n → K)} (hY : IsFlipflopSub σ Y) :
    QNondeg (Y ⊔ dFlipSub σ Y) ∧ QPlus (Y ⊔ dFlipSub σ Y) ∧
      Module.finrank K ↥(Y ⊔ dFlipSub σ Y) = 2 * Module.finrank K Y ∧
      dFlipSub σ (Y ⊔ dFlipSub σ Y) = Y ⊔ dFlipSub σ Y := by
  have hdisj : Y ⊓ dFlipSub σ Y = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    obtain ⟨hyY, hyd⟩ := Submodule.mem_inf.mp hy
    have hdy : dFlip σ y ∈ Y := (mem_dFlipSub hσ).mp hyd
    refine hY.nondeg y hyY fun v hv => ?_
    have h1 : flipHerm σ v y = 0 := by
      have hp := polar_eq_zero_of_mem_qSing hY.total hv hdy
      simpa only [flipHerm] using hp
    have h2 := flipHerm_conj hσ y v
    rw [h1] at h2
    exact (map_eq_zero_iff σ σ.injective).mp h2
  have hrad : (Y ⊔ dFlipSub σ Y) ⊓ qPerp n K (Y ⊔ dFlipSub σ Y) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨hzW, hzp⟩ := Submodule.mem_inf.mp hz
    obtain ⟨y₁, hy₁, w, hw, hzw⟩ := Submodule.mem_sup.mp hzW
    obtain ⟨y₂, hy₂, rfl⟩ : ∃ y₂ ∈ Y, dFlip σ y₂ = w :=
      ⟨dFlip σ w, (mem_dFlipSub hσ).mp hw, dFlip_dFlip hσ w⟩
    have hy₂0 : y₂ = 0 := by
      refine hY.nondeg y₂ hy₂ fun u hu => ?_
      have h := (mem_qPerp.mp hzp) u (Submodule.mem_sup_left hu)
      rw [← hzw] at h
      rw [polar_add_right, polar_eq_zero_of_mem_qSing hY.total hu hy₁, zero_add] at h
      exact (flipHerm_eq_zero_iff hσ).mp (by simpa only [flipHerm] using h)
    have hdy₂ : dFlip σ y₂ = 0 := by
      rw [hy₂0]
      ext x
      cases x <;> simp [dFlip]
    have hz1 : z = y₁ := by
      rw [← hzw, hdy₂, add_zero]
    have hy₁0 : y₁ = 0 := by
      refine hY.nondeg y₁ hy₁ fun u hu => ?_
      have hmem : dFlip σ u ∈ Y ⊔ dFlipSub σ Y :=
        Submodule.mem_sup_right (Submodule.subset_span ⟨u, hu, rfl⟩)
      have h := (mem_qPerp.mp hzp) (dFlip σ u) hmem
      rw [hz1, polar_comm] at h
      exact h
    rw [hz1, hy₁0]
  have hdim : Module.finrank K ↥(Y ⊔ dFlipSub σ Y) = 2 * Module.finrank K Y := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq Y (dFlipSub σ Y)
    rw [hdisj, finrank_bot, finrank_dFlipSub hσ] at h
    omega
  have hinv : dFlipSub σ (Y ⊔ dFlipSub σ Y) = Y ⊔ dFlipSub σ Y := by
    rw [dFlipSub_sup hσ, dFlipSub_dFlipSub hσ, sup_comm]
  exact ⟨hrad, ⟨Y, le_sup_left, hY.total, hdim.symm⟩, hdim, hinv⟩

theorem IsFlipflopSub.exists_pt_orth (hσ : IsUnitaryInvolution σ)
    {Y : Submodule K (Fin n ⊕ Fin n → K)} (hY : IsFlipflopSub σ Y)
    (hd : Module.finrank K Y + 2 ≤ n) :
    ∃ p, IsFlipflopPt σ p ∧ p ≤ qPerp n K Y ∧ p ≤ flipOrth σ Y := by
  have hσ' : ∀ x, σ (σ x) = x := hσ.invol
  obtain ⟨hWnd, hWplus, hWdim, -⟩ := hY.sup_dFlipSub hσ'
  have hZnd : QNondeg (qPerp n K (Y ⊔ dFlipSub σ Y)) := hWnd.qPerp
  have hZplus : QPlus (qPerp n K (Y ⊔ dFlipSub σ Y)) := hWplus.qPerp hWnd
  have hZinv : dFlipSub σ (qPerp n K (Y ⊔ dFlipSub σ Y)) =
      qPerp n K (Y ⊔ dFlipSub σ Y) := by
    rw [← qPerp_dFlipSub hσ' (Y ⊔ dFlipSub σ Y), dFlipSub_sup hσ', dFlipSub_dFlipSub hσ',
      sup_comm]
  have hZdim := finrank_qPerp (n := n) (K := K) (Y ⊔ dFlipSub σ Y)
  rw [hWdim] at hZdim
  have h4 : 4 ≤ Module.finrank K ↥(qPerp n K (Y ⊔ dFlipSub σ Y)) := by omega
  have hZne : qPerp n K (Y ⊔ dFlipSub σ Y) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h4
    omega
  obtain ⟨u, hu, v, hv, hne⟩ :=
    exists_flipHerm_ne_zero_of_dFlipSub hσ' hZnd hZinv hZne
  obtain ⟨p, hpZ, hp⟩ :=
    exists_isFlipflopPt_le_of_qPlus hσ hZnd hZplus h4 ⟨u, hu, v, hv, hne⟩
  refine ⟨p, hp, hpZ.trans ?_, hpZ.trans ?_⟩
  · exact qPerp_antitone (le_sup_left : Y ≤ Y ⊔ dFlipSub σ Y)
  · rw [flipOrth_eq_qPerp_dFlipSub hσ']
    exact qPerp_antitone (le_sup_right : dFlipSub σ Y ≤ Y ⊔ dFlipSub σ Y)

theorem IsFlipflopSub.exists_two_solids (hσ : ∀ x, σ (σ x) = x)
    {X : Submodule K (Fin n ⊕ Fin n → K)} (hX : IsFlipflopSub σ X)
    (hd : Module.finrank K X + 1 = n) :
    ∃ M M', IsSolid σ M ∧ IsSolid σ M' ∧ X ≤ M ∧ X ≤ M' ∧
      Even (n - Module.finrank K ↥(M ⊓ stdLag n K)) ∧
      ¬ Even (n - Module.finrank K ↥(M' ⊓ stdLag n K)) ∧
      ∀ N, (quadPlusForm n K).IsLagrangian N → X ≤ N → N = M ∨ N = M' := by
  have hn : Module.finrank K (Fin n ⊕ Fin n → K) = 2 * n := finrank_flipSpace n K
  have hE : (quadPlusForm n K).IsLagrangian (stdLag n K) := isLagrangian_stdLag n K
  have hXsing : (quadPlusForm n K).IsTotallySingular X :=
    (qSing_iff_isTotallySingular X).mp hX.total
  obtain ⟨Y, Y', hne, hY, hY', hXY, hXY', huniq⟩ :=
    QuadForm.exists_isLagrangian_pair (Φ := quadPlusForm n K) hn hE hXsing hd
  have hrad : ∀ M, (quadPlusForm n K).IsLagrangian M → X ≤ M →
      M ⊓ dFlipSub σ M = ⊥ := by
    intro M hM hXM
    have heven : Even (Module.finrank K ↥(M ⊓ dFlipSub σ M)) :=
      even_finrank_inf_dFlipSub hσ hM
    have hMsing : QSing M := (qSing_iff_isTotallySingular M).mpr hM.1
    have hRflip : M ⊓ dFlipSub σ M ≤ flipOrth σ X := by
      intro r hr
      obtain ⟨hrM, hrσ⟩ := Submodule.mem_inf.mp hr
      rw [mem_flipOrth]
      intro x hx
      have hdr : dFlip σ r ∈ M := (mem_dFlipSub hσ).mp hrσ
      have hp := polar_eq_zero_of_mem_qSing hMsing (hXM hx) hdr
      simpa only [flipHerm] using hp
    have hRX : (M ⊓ dFlipSub σ M) ⊓ X = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro r hr
      obtain ⟨hrR, hrX⟩ := Submodule.mem_inf.mp hr
      have hmem : r ∈ X ⊓ flipOrth σ X := Submodule.mem_inf.mpr ⟨hrX, hRflip hrR⟩
      rw [inf_flipOrth_eq_bot hσ hX] at hmem
      simpa using hmem
    have hdimR : Module.finrank K ↥(M ⊓ dFlipSub σ M) ≤ 1 := by
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq (M ⊓ dFlipSub σ M) X
      rw [hRX, finrank_bot, add_zero] at h1
      have h2 := Submodule.finrank_mono
        (sup_le inf_le_left hXM : (M ⊓ dFlipSub σ M) ⊔ X ≤ M)
      have h3 := hM.2
      rw [hn] at h3
      omega
    have h0 : Module.finrank K ↥(M ⊓ dFlipSub σ M) = 0 := by
      rw [Nat.even_iff] at heven
      omega
    exact Submodule.finrank_eq_zero.mp h0
  have hsolid : ∀ M, (quadPlusForm n K).IsLagrangian M → X ≤ M → IsSolid σ M := by
    intro M hM hXM
    have hR := hrad M hM hXM
    refine ⟨⟨(qSing_iff_isTotallySingular M).mpr hM.1, ?_⟩, ?_⟩
    · intro u hu hper
      have hu' : u ∈ flipOrth σ M :=
        mem_flipOrth.mpr fun v hv => (flipHerm_eq_zero_iff hσ).mp (hper v hv)
      rw [flipOrth_eq_dFlipSub_of_isLagrangian hσ hM] at hu'
      have hmem : u ∈ M ⊓ dFlipSub σ M := Submodule.mem_inf.mpr ⟨hu, hu'⟩
      rw [hR] at hmem
      simpa using hmem
    · have h := hM.2
      rw [hn] at h
      omega
  have hMY : IsSolid σ Y := hsolid Y hY hXY
  have hMY' : IsSolid σ Y' := hsolid Y' hY' hXY'
  have hYY' : Module.finrank K ↥(Y ⊓ Y') + 1 = n := by
    have hmono := Submodule.finrank_mono (le_inf hXY hXY' : X ≤ Y ⊓ Y')
    have hle := Submodule.finrank_mono (inf_le_left : Y ⊓ Y' ≤ Y)
    have hYn : Module.finrank K Y = n := hMY.2
    have hne' : Module.finrank K ↥(Y ⊓ Y') ≠ n := by
      intro hEq
      have h1 : Y ⊓ Y' = Y := Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
      have h2 : Y ≤ Y' := h1 ▸ inf_le_right
      exact hne (hY.eq_of_le hY'.1 h2)
    omega
  have hpar := QuadForm.IsLagrangian.even_add_add (Φ := quadPlusForm n K) (n := n) hn hY hY' hE
  have h1 : n - Module.finrank K ↥(Y ⊓ Y') = 1 := by omega
  rw [h1] at hpar
  rw [Nat.even_iff] at hpar
  have hcases : (Even (n - Module.finrank K ↥(Y ⊓ stdLag n K)) ∧
      ¬ Even (n - Module.finrank K ↥(Y' ⊓ stdLag n K))) ∨
      (Even (n - Module.finrank K ↥(Y' ⊓ stdLag n K)) ∧
      ¬ Even (n - Module.finrank K ↥(Y ⊓ stdLag n K))) := by
    rcases Nat.mod_two_eq_zero_or_one (n - Module.finrank K ↥(Y ⊓ stdLag n K)) with ha | ha
    · rcases Nat.mod_two_eq_zero_or_one (n - Module.finrank K ↥(Y' ⊓ stdLag n K)) with hb | hb
      · omega
      · exact Or.inl ⟨Nat.even_iff.mpr ha,
          fun hE' => by rw [Nat.even_iff] at hE'; omega⟩
    · rcases Nat.mod_two_eq_zero_or_one (n - Module.finrank K ↥(Y' ⊓ stdLag n K)) with hb | hb
      · exact Or.inr ⟨Nat.even_iff.mpr hb,
          fun hE' => by rw [Nat.even_iff] at hE'; omega⟩
      · omega
  rcases hcases with ⟨hb, hna⟩ | ⟨ha, hnb⟩
  · exact ⟨Y, Y', hMY, hMY', hXY, hXY', hb, hna, huniq⟩
  · refine ⟨Y', Y, hMY', hMY, hXY', hXY, ha, hnb, fun N hN hXN => ?_⟩
    rcases huniq N hN hXN with h | h
    · exact Or.inr h
    · exact Or.inl h

theorem IsFlipflopSub.exists_solid_le (hσ : IsUnitaryInvolution σ)
    {Y : Submodule K (Fin n ⊕ Fin n → K)} (hY : IsFlipflopSub σ Y)
    (hd : Module.finrank K Y < n) :
    ∃ M M', IsSolid σ M ∧ IsSolid σ M' ∧ Y ≤ M ∧ Y ≤ M' ∧
      Even (n - Module.finrank K ↥(M ⊓ stdLag n K)) ∧
      ¬ Even (n - Module.finrank K ↥(M' ⊓ stdLag n K)) := by
  suffices h : ∀ k, ∀ Y : Submodule K (Fin n ⊕ Fin n → K), IsFlipflopSub σ Y →
      n - Module.finrank K Y = k → Module.finrank K Y < n →
      ∃ M M', IsSolid σ M ∧ IsSolid σ M' ∧ Y ≤ M ∧ Y ≤ M' ∧
        Even (n - Module.finrank K ↥(M ⊓ stdLag n K)) ∧
        ¬ Even (n - Module.finrank K ↥(M' ⊓ stdLag n K)) from h _ Y hY rfl hd
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro Y hY hk hdim
    by_cases hlast : Module.finrank K Y + 1 = n
    · obtain ⟨M, M', hM, hM', hYM, hYM', hev, hodd, -⟩ :=
        hY.exists_two_solids hσ.invol hlast
      exact ⟨M, M', hM, hM', hYM, hYM', hev, hodd⟩
    · have h2 : Module.finrank K Y + 2 ≤ n := by omega
      obtain ⟨p, hp, hpq, hpf⟩ := hY.exists_pt_orth hσ h2
      obtain ⟨hYp, hdisj⟩ : IsFlipflopSub σ (p ⊔ Y) ∧ Disjoint p Y :=
        IsFlipflopSub.sup_of_orth hσ.invol hp.1 hY hpq hpf
      have hYp' : IsFlipflopSub σ (Y ⊔ p) := by rwa [sup_comm] at hYp
      have hdisj' : Disjoint Y p := hdisj.symm
      have hdimYp : Module.finrank K ↥(Y ⊔ p) = Module.finrank K Y + 1 := by
        have h := Submodule.finrank_sup_add_finrank_inf_eq Y p
        rw [disjoint_iff.mp hdisj', finrank_bot, hp.2] at h
        omega
      have hk' : n - Module.finrank K ↥(Y ⊔ p) < k := by omega
      have hlt' : Module.finrank K ↥(Y ⊔ p) < n := by omega
      obtain ⟨M, M', hM, hM', hYM, hYM', hev, hodd⟩ :=
        ih _ hk' (Y ⊔ p) hYp' rfl hlt'
      exact ⟨M, M', hM, hM', le_trans le_sup_left hYM, le_trans le_sup_left hYM', hev, hodd⟩

def solidWalks (σ : K ≃+* K) (n : ℕ) :
    ∀ x : FlipPt σ n, Set ((flipGraph σ n).Walk x x) :=
  fun _ => {c | ∃ M : Submodule K (Fin n ⊕ Fin n → K), IsSolid σ M ∧ ∀ y ∈ c.support, y.1 ≤ M}

theorem mem_solidWalks_iff {x : FlipPt σ n} {c : (flipGraph σ n).Walk x x} :
    c ∈ solidWalks σ n x ↔ ∃ M, IsSolid σ M ∧ ∀ y ∈ c.support, y.1 ≤ M := Iff.rfl

theorem reverse_mem_solidWalks {x : FlipPt σ n} {c : (flipGraph σ n).Walk x x}
    (hc : c ∈ solidWalks σ n x) : c.reverse ∈ solidWalks σ n x := by
  obtain ⟨M, hM, hsupp⟩ := hc
  exact ⟨M, hM, fun y hy => hsupp y (by simpa [SimpleGraph.Walk.support_reverse] using hy)⟩

theorem mem_solidWalks_of_le (hσ : IsUnitaryInvolution σ)
    {U : Submodule K (Fin n ⊕ Fin n → K)} (hU : IsFlipflopSub σ U)
    {x : FlipPt σ n} {c : (flipGraph σ n).Walk x x}
    (hc : ∀ y ∈ c.support, y.1 ≤ U) : c ∈ solidWalks σ n x := by
  by_cases hdim : Module.finrank K U = n
  · exact ⟨U, ⟨hU, hdim⟩, hc⟩
  · have hlt : Module.finrank K U < n := lt_of_le_of_ne hU.finrank_le hdim
    obtain ⟨M, -, hM, -, hUM, -, -, -⟩ := hU.exists_solid_le hσ hlt
    exact ⟨M, hM, fun y hy => le_trans (hc y hy) hUM⟩

end CFSG.ClassicalInvolution.PhanDn
