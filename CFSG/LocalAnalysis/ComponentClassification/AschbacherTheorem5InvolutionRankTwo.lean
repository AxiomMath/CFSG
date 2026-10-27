module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionThree
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionFixed

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace Involution

open SectionSix AschbacherToolkit

theorem not_isMulCommutative_of_quaternion {Q : Type} [Group Q] {E : Subgroup Q}
    (hE : AschbacherTheorem3.IsQuaternionTwoGroup E) (hc : IsMulCommutative E) : False := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hE
  set m := 2 ^ (n - 2)
  have hm2 : 2 ≤ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : NeZero (2 * m) := ⟨by omega⟩
  have h := congrArg e (mul_comm' (e.symm (QuaternionGroup.a 1)) (e.symm (QuaternionGroup.xa 0)))
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
    QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a, QuaternionGroup.xa.injEq] at h
  have h2 : ((2 : ℕ) : ZMod (2 * m)) = 0 := by
    have : (0 : ZMod (2 * m)) - 1 = 0 + 1 := h
    have h' : (2 : ZMod (2 * m)) = 0 := by
      calc (2 : ZMod (2 * m)) = (0 + 1) - (0 - 1) := by ring
        _ = 0 := by rw [this]; ring
    exact_mod_cast h'
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem isCyclic_of_comm_of_unique {Q : Type} [Group Q] [Finite Q] {E : Subgroup Q}
    (hE2 : IsPGroup 2 E) (hEc : IsMulCommutative E)
    (huniq : ∀ a ∈ E, ∀ b ∈ E, orderOf a = 2 → orderOf b = 2 → a = b) : IsCyclic E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr : CFSG.Open.pRank 2 E ≤ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨F, hFE, hF, hcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
      (p := 2) (H := E) (k := 2) (by omega)
    have hsub : ¬ (F : Set Q) ⊆ {1, (1 : Q)} := by
      intro h
      have := card_le_two_of_subset h
      rw [hcard] at this
      norm_num at this
    obtain ⟨x, hx, hxne⟩ := Set.not_subset.mp hsub
    have hx1 : x ≠ 1 := fun h => hxne (Or.inl h)
    have hsub2 : ¬ (F : Set Q) ⊆ {1, x} := by
      intro h
      have := card_le_two_of_subset h
      rw [hcard] at this
      norm_num at this
    obtain ⟨y, hy, hyne⟩ := Set.not_subset.mp hsub2
    have hy1 : y ≠ 1 := fun h => hyne (Or.inl h)
    exact hyne (Or.inr (huniq y (hFE hy) x (hFE hx) (orderOf_eq_prime (hF.2 y hy) hy1)
      (orderOf_eq_prime (hF.2 x hx) hx1)))
  rcases cyclic_or_quaternion_of_pRank_le_one hE2 hr with hcyc | hq
  · exact hcyc
  · exact (not_isMulCommutative_of_quaternion hq hEc).elim

theorem pRank_le_top_subtype {Q : Type*} [Group Q] [Finite Q] (X : Subgroup Q) :
    CFSG.Open.pRank 2 X ≤ CFSG.Open.pRank 2 (⊤ : Subgroup X) := by
  obtain ⟨E, hEX, hE, hcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two X
  refine CFSG.SectionRank.le_pRank one_lt_two (E := E.subgroupOf X) le_top ?_ ?_
  · have hc := hE.1
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => Subtype.ext ?_⟩
    · have := congrArg Subtype.val (mul_comm' (⟨(a : X), a.2⟩ : E) ⟨(b : X), b.2⟩)
      exact Subtype.ext this
    · rw [Subgroup.coe_pow]
      exact hE.2 _ hx
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv, hcard]

theorem exists_two_involutions {Q : Type*} [Group Q] [Finite Q] {E : Subgroup Q}
    (hE : 2 ≤ CFSG.Open.pRank 2 E) :
    ∃ s ∈ E, ∃ u ∈ E, orderOf s = 2 ∧ orderOf u = 2 ∧ s ≠ u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, hFE, hF, hcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
    (p := 2) (H := E) (k := 2) hE
  have hsub : ¬ (F : Set Q) ⊆ {1, (1 : Q)} := by
    intro h
    have := card_le_two_of_subset h
    rw [hcard] at this
    norm_num at this
  obtain ⟨x, hx, hxne⟩ := Set.not_subset.mp hsub
  have hx1 : x ≠ 1 := fun h => hxne (Or.inl h)
  have hsub2 : ¬ (F : Set Q) ⊆ {1, x} := by
    intro h
    have := card_le_two_of_subset h
    rw [hcard] at this
    norm_num at this
  obtain ⟨y, hy, hyne⟩ := Set.not_subset.mp hsub2
  have hy1 : y ≠ 1 := fun h => hyne (Or.inl h)
  exact ⟨x, hFE hx, y, hFE hy, orderOf_eq_prime (hF.2 x hx) hx1,
    orderOf_eq_prime (hF.2 y hy) hy1, fun h => hyne (Or.inr h.symm)⟩

theorem mem_zpowers_or_mem_zpowers {Q : Type} [Group Q] [Finite Q] {E : Subgroup Q}
    (hE : IsCyclic E) {x y : Q} (hx : x ∈ E) (hy : y ∈ E)
    (hx2 : IsPGroup 2 (Subgroup.zpowers x)) (hy2 : IsPGroup 2 (Subgroup.zpowers y)) :
    x ∈ Subgroup.zpowers y ∨ y ∈ Subgroup.zpowers x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ {x y : Q} (hx : x ∈ E) (hy : y ∈ E), orderOf x ∣ orderOf y →
      x ∈ Subgroup.zpowers y := by
    intro x y hx hy hdvd
    have hle : Subgroup.zpowers (⟨x, hx⟩ : E) ≤ Subgroup.zpowers ⟨y, hy⟩ := by
      rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers,
        Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact hdvd
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hle (Subgroup.mem_zpowers _))
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩
  obtain ⟨a, ha⟩ := hx2.exists_card_eq
  obtain ⟨b, hb⟩ := hy2.exists_card_eq
  rw [Nat.card_zpowers] at ha hb
  rcases le_total a b with hab | hab
  · exact Or.inl (key hx hy (by rw [ha, hb]; exact Nat.pow_dvd_pow 2 hab))
  · exact Or.inr (key hy hx (by rw [ha, hb]; exact Nat.pow_dvd_pow 2 hab))

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem exists_fixed_noncentral (hin : SectionSevenBase) (hC : Counterexample G D r Abar)
    {t g : G} (h : Hyp71 D t g) {k : Fin r}
    (hfix : (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj t).toMonoidHom =
      aschbacherThm5Preimage D (Abar k))
    (hrank : 2 ≤ CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar k))) :
    ∃ y ∈ Abar k, onQuotient D ⟨t, h.mem⟩ y = y ∧ IsPGroup 2 (Subgroup.zpowers y) ∧
      y ∉ Subgroup.centralizer (Abar k : Set (D ⧸ aschbacherThm5OddCore D)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hC.hyp
  set σ := onQuotient D ⟨t, h.mem⟩
  have ht2 : t ^ 2 = 1 := by rw [← h.orderOf_eq]; exact pow_orderOf_eq_one t
  have hσ : ∀ q, σ (σ q) = q := onQuotient_involutive ht2
  have hσ2 : σ ^ 2 = 1 := by
    ext q
    rw [pow_two, MulAut.mul_apply, hσ, MulAut.one_apply]
  have hmapk : (Abar k).map (σ : (D ⧸ aschbacherThm5OddCore D) →* (D ⧸ aschbacherThm5OddCore D)) =
      Abar k := map_onQuotient_factor ⟨t, h.mem⟩ hfix
  by_contra hno
  push Not at hno
  set X := Abar k
  have hX : Group.IsPerfect X := semisimple_perfect _ (hyp.hsemisimple k)
  set α := restrictAut σ X hmapk
  have hα : α ^ 2 = 1 := restrictAut_sq σ hσ2 X hmapk
  obtain ⟨P, hPα⟩ := exists_invariant_sylow_two α hα
  set Z := fixedIn (P : Subgroup X) (α : X →* X)
  have hcen : ∀ x : X, α x = x → IsPGroup 2 (Subgroup.zpowers x) → x ∈ Subgroup.center X := by
    intro x hαx hx2
    have hx2' : IsPGroup 2 (Subgroup.zpowers (x : D ⧸ aschbacherThm5OddCore D)) := by
      have := hx2.map X.subtype
      rwa [MonoidHom.map_zpowers] at this
    have hxc := hno x x.2 (congrArg Subtype.val hαx) hx2'
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc y y.2)
  have hZc : Z ≤ Subgroup.center X := fun x hx =>
    hcen x hx.2 (P.isPGroup'.to_le (Subgroup.zpowers_le.mpr hx.1))
  have hZP : Z ≤ (P : Subgroup X) := fixedIn_le _ _
  have hZα : Z.map (α : X →* X) = Z := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [hx.2]
      exact hx
    · intro x hx
      exact ⟨x, hx, hx.2⟩
  obtain ⟨m, hmk⟩ := exists_ne hC k
  have hZcyc : IsCyclic Z := by
    apply isCyclic_of_comm_of_unique (P.isPGroup'.to_le hZP)
    · exact ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hZc b.2) a)⟩⟩
    · intro a ha b hb ha2 hb2
      by_contra hab
      apply no_commuting_pair hin hC h (a := (a : D ⧸ aschbacherThm5OddCore D)) (b := b)
        (by rw [Subgroup.orderOf_coe]; exact ha2) (by rw [Subgroup.orderOf_coe]; exact hb2)
        (congrArg Subtype.val (Subgroup.mem_center_iff.mp (hZc hb) a))
        (fun h' => hab (Subtype.ext h')) (congrArg Subtype.val ha.2)
        (congrArg Subtype.val hb.2) m (mem_centralizer_factor hyp hmk a.2)
        (mem_centralizer_factor hyp hmk b.2)
  have hPnt : Nontrivial (P : Subgroup X) := by
    have : Nontrivial X := semisimple_nontrivial _ (hyp.hsemisimple k)
    have heven : Even (Nat.card X) := even_card_of_perfect
    rw [Subgroup.nontrivial_iff_ne_bot]
    exact P.ne_bot_of_dvd_card (even_iff_two_dvd.mp heven)
  set β := restrictAut α (P : Subgroup X) hPα
  have hβ : β ^ 2 = 1 := restrictAut_sq α hα _ hPα
  obtain ⟨p, hp1, hβp⟩ := exists_fixed_ne_one P.isPGroup' β hβ
  have hZne : Z ≠ ⊥ := by
    intro hbot
    have hpZ : (p : X) ∈ Z := ⟨p.2, congrArg Subtype.val hβp⟩
    rw [hbot, Subgroup.mem_bot] at hpZ
    exact hp1 (Subtype.ext hpZ)
  have hrankX : 2 ≤ CFSG.Open.pRank 2 (P : Subgroup X) := by
    rw [(CFSG.SectionRank.pRank_sylow P).1]
    exact hrank.trans ((pRank_preimage_le _).trans (pRank_le_top_subtype _))
  obtain ⟨s, hsP, u, huP, hs, hu, hsu⟩ := exists_two_involutions hrankX
  exact false_of_fixed_central hX α hα P hPα Z hZc hZP hZα hZcyc hZne
    (fun p hp hαp => ⟨hp, hαp⟩) hsP huP hs hu hsu

theorem three_fixed_impossible (hin : SectionSevenBase) (hC : Counterexample G D r Abar)
    {t g : G} (h : Hyp71 D t g) {k₀ k₁ k₂ : Fin r} (h01 : k₀ ≠ k₁) (h02 : k₀ ≠ k₂)
    (h12 : k₁ ≠ k₂)
    (hfix₀ : (aschbacherThm5Preimage D (Abar k₀)).map (MulAut.conj t).toMonoidHom =
      aschbacherThm5Preimage D (Abar k₀))
    (hfix₁ : (aschbacherThm5Preimage D (Abar k₁)).map (MulAut.conj t).toMonoidHom =
      aschbacherThm5Preimage D (Abar k₁))
    (hrank₀ : 2 ≤ CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar k₀)))
    (hrank₁ : 2 ≤ CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar k₁))) : False := by
  have hyp := hC.hyp
  obtain ⟨y₀, hy₀, hσy₀, hy₀2, hy₀c⟩ := exists_fixed_noncentral hin hC h hfix₀ hrank₀
  obtain ⟨y₁, hy₁, hσy₁, hy₁2, hy₁c⟩ := exists_fixed_noncentral hin hC h hfix₁ hrank₁
  set σ := onQuotient D ⟨t, h.mem⟩
  have hcomm : y₀ * y₁ = y₁ * y₀ := hyp.hcomm k₀ k₁ h01 y₀ hy₀ y₁ hy₁
  set E : Subgroup (D ⧸ aschbacherThm5OddCore D) :=
    Subgroup.zpowers y₀ ⊔ Subgroup.zpowers y₁ with hEdef
  have hEc : IsMulCommutative E := by
    rw [hEdef, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union]
    apply Subgroup.isMulCommutative_closure
    intro a ha b hb _
    simp only [Set.mem_union, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Commute.refl _
    · exact hcomm
    · exact hcomm.symm
    · exact Commute.refl _
  have hE2 : IsPGroup 2 E := by
    apply IsPGroup.to_sup_of_normal_right' hy₀2 hy₁2
    rw [Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨n, rfl⟩
    exact ((show Commute y₁ y₀ from hcomm.symm).zpow_left n).eq
  have hEσ : E ≤ AschbacherToolkit.fixedSubgroup σ :=
    sup_le (Subgroup.zpowers_le.mpr (AschbacherToolkit.mem_fixedSubgroup.mpr hσy₀))
      (Subgroup.zpowers_le.mpr (AschbacherToolkit.mem_fixedSubgroup.mpr hσy₁))
  have hEk₂ : E ≤ Subgroup.centralizer (Abar k₂ : Set (D ⧸ aschbacherThm5OddCore D)) :=
    sup_le (Subgroup.zpowers_le.mpr (mem_centralizer_factor hyp h02.symm hy₀))
      (Subgroup.zpowers_le.mpr (mem_centralizer_factor hyp h12.symm hy₁))
  have hEcyc : IsCyclic E := by
    apply isCyclic_of_comm_of_unique hE2 hEc
    intro a ha b hb ha2 hb2
    by_contra hab
    exact no_commuting_pair hin hC h ha2 hb2
      (congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : E) ⟨b, hb⟩)) hab
      (AschbacherToolkit.mem_fixedSubgroup.mp (hEσ ha))
      (AschbacherToolkit.mem_fixedSubgroup.mp (hEσ hb)) k₂ (hEk₂ ha) (hEk₂ hb)
  rcases mem_zpowers_or_mem_zpowers hEcyc
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers y₀))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers y₁)) hy₀2 hy₁2 with h0 | h1
  · exact hy₀c ((Subgroup.zpowers_le.mpr (mem_centralizer_factor hyp h01 hy₁)) h0)
  · exact hy₁c ((Subgroup.zpowers_le.mpr (mem_centralizer_factor hyp h01.symm hy₀)) h1)

theorem r_eq_two_and_rank (hin : SectionSevenBase) (hC : Counterexample G D r Abar)
    {t g : G} (h : Hyp71 D t g) :
    r = 2 ∧ ∀ k, 2 ≤ CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar k)) := by
  by_cases hmove : ∃ i, (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj t).toMonoidHom ≠
      aschbacherThm5Preimage D (Abar i)
  · obtain ⟨i, hi⟩ := hmove
    obtain ⟨hr2, -, hri⟩ := lemma_7_3 hin hC h i hi
    refine ⟨hr2, fun k => ?_⟩
    obtain ⟨x, -, hxk⟩ := hin.lemma_6_3 hC i k
    rw [← hxk, pRank_map_conj]
    exact hri
  push Not at hmove
  have hrank : ∀ k, 2 ≤ CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar k)) := by
    intro k
    by_contra hk
    push Not at hk
    exact rankOne_fixed_impossible hin hC h hmove (i := k) (by omega)
  refine ⟨?_, hrank⟩
  by_contra hr2
  have h3 : 3 ≤ r := by have := two_le hC; omega
  exact three_fixed_impossible hin hC h (k₀ := ⟨0, by omega⟩) (k₁ := ⟨1, by omega⟩)
    (k₂ := ⟨2, by omega⟩) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (by simp [Fin.ext_iff]) (hmove _) (hmove _) (hrank _) (hrank _)

end Involution

end CFSG.ComponentClassification.AschbacherTheorem5
