module

public import CFSG.LocalAnalysis.OddStandard.ThmCTBasic

public section

namespace CFSG.OddStandard.ThmC.T

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open scoped commutatorElement

@[expose] def symp (s t : F4c × F4c) : F4c := s.1 * t.2 + t.1 * s.2

theorem line_lemma : ∀ a b a' b' : F4c, (a ≠ 0 ∨ b ≠ 0) → a * b' + a' * b = 0 →
    ∃ l : F4c, a' = l * a ∧ b' = l * b := by decide +kernel

theorem d_lemma : ∀ ζ d c0 : F4c, ζ ≠ 0 → d ≠ 0 → d ≠ ζ →
    (c0 = 0 ∨ c0 = ζ ∨ c0 = d ∨ c0 = ζ + d) := by decide +kernel

theorem t_lemma : ∀ s1 s2 t : F4c × F4c, symp s1 s2 ≠ 0 →
    (symp s1 t = 0 ∨ symp s1 t = symp s1 s2) → (symp s2 t = 0 ∨ symp s2 t = symp s1 s2) →
    (t = 0 ∨ t = s1 ∨ t = s2 ∨ t = s1 + s2) := by decide +kernel

theorem central_mul (c d : F4c) : (⟨0, 0, c⟩ : Tc) * ⟨0, 0, d⟩ = ⟨0, 0, c + d⟩ := by
  refine UT3.ext ?_ ?_ ?_ <;> simp [UT3.mul_def]

theorem exists_finset_proj {H : Subgroup Tc} (hZ : ¬ Subgroup.center Tc ≤ H) :
    ∃ F : Finset (F4c × F4c), F.card ≤ 4 ∧ ∀ h ∈ H, (h.a, h.b) ∈ F := by
  classical
  obtain ⟨z, hzZ, hzH⟩ := IsConcreteLE.not_le_iff_exists.mp hZ
  rw [mem_center_iff] at hzZ
  have hc0 : (⟨0, 0, z.c⟩ : Tc) ∉ H := by
    have : z = ⟨0, 0, z.c⟩ := UT3.ext hzZ.1 hzZ.2 rfl
    rwa [← this]
  have hcomm : ∀ h ∈ H, ∀ h' ∈ H,
      (⟨0, 0, symp (h.a, h.b) (h'.a, h'.b)⟩ : Tc) ∈ H := by
    intro h hh h' hh'
    have := H.mul_mem (H.mul_mem (H.mul_mem hh hh') (H.inv_mem hh)) (H.inv_mem hh')
    rw [← commutatorElement_def, comm_eq] at this
    exact this
  by_cases hdet : ∀ h ∈ H, ∀ h' ∈ H, symp (h.a, h.b) (h'.a, h'.b) = 0
  · by_cases hs : ∀ h ∈ H, (h.a, h.b) = (0, 0)
    · exact ⟨{(0, 0)}, by simp, fun h hh => by simp [hs h hh]⟩
    · push Not at hs
      obtain ⟨h0, hh0, hne⟩ := hs
      have hne' : h0.a ≠ 0 ∨ h0.b ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hne (by rw [hcon.1, hcon.2])
      refine ⟨Finset.univ.image (fun l : F4c => (l * h0.a, l * h0.b)), ?_, ?_⟩
      · refine Finset.card_image_le.trans ?_
        rw [Finset.card_univ]
        exact (by decide : Fintype.card F4c = 4).le
      · intro h hh
        obtain ⟨l, hl1, hl2⟩ := line_lemma h0.a h0.b h.a h.b hne' (hdet h0 hh0 h hh)
        exact Finset.mem_image.2 ⟨l, Finset.mem_univ _, by rw [← hl1, ← hl2]⟩
  · push Not at hdet
    obtain ⟨h1, hh1, h2, hh2, hne⟩ := hdet
    have hζ := hcomm h1 hh1 h2 hh2
    have hD : ∀ d d' : F4c, (⟨0, 0, d⟩ : Tc) ∈ H → (⟨0, 0, d'⟩ : Tc) ∈ H →
        (⟨0, 0, d + d'⟩ : Tc) ∈ H := fun d d' hd hd' => by
      rw [← central_mul]
      exact H.mul_mem hd hd'
    have key : ∀ d : F4c, (⟨0, 0, d⟩ : Tc) ∈ H →
        d = 0 ∨ d = symp (h1.a, h1.b) (h2.a, h2.b) := by
      intro d hd
      by_contra hcon
      push Not at hcon
      rcases d_lemma _ d z.c hne hcon.1 hcon.2 with h | h | h | h
      · exact hc0 (by rw [h]; exact H.one_mem)
      · exact hc0 (by rw [h]; exact hζ)
      · exact hc0 (by rw [h]; exact hd)
      · exact hc0 (by rw [h]; exact hD _ _ hζ hd)
    refine ⟨{0, (h1.a, h1.b), (h2.a, h2.b), (h1.a + h2.a, h1.b + h2.b)}, Finset.card_le_four, ?_⟩
    intro h hh
    have hd1 := key _ (hcomm h1 hh1 h hh)
    have hd2 := key _ (hcomm h2 hh2 h hh)
    have := t_lemma (h1.a, h1.b) (h2.a, h2.b) (h.a, h.b) hne hd1 hd2
    simpa [Prod.ext_iff] using this

@[expose] def proj : Tc →* Multiplicative (F4c × F4c) where
  toFun x := Multiplicative.ofAdd (x.a, x.b)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem mem_ker_proj {x : Tc} : x ∈ proj.ker ↔ x ∈ Subgroup.center Tc := by
  rw [MonoidHom.mem_ker, mem_center_iff]
  constructor
  · intro h
    have h' : (x.a, x.b) = 0 := h
    exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  · rintro ⟨h1, h2⟩
    show Multiplicative.ofAdd (x.a, x.b) = 1
    rw [h1, h2]
    rfl

theorem card_le_of_not_center_le {H : Subgroup Tc} (hZ : ¬ Subgroup.center Tc ≤ H) :
    Nat.card H ≤ 4 * Nat.card ↥(H ⊓ Subgroup.center Tc) ∧
      Nat.card ↥(H ⊓ Subgroup.center Tc) ≤ 2 := by
  classical
  constructor
  ·
    set g : H →* Multiplicative (F4c × F4c) := proj.comp H.subtype with hg
    have h1 := Subgroup.card_ker_mul_card_range g
    have hker : Nat.card g.ker = Nat.card ↥(H ⊓ Subgroup.center Tc) := by
      refine Nat.card_congr
        { toFun := fun x => ⟨x.1.1, x.1.2, mem_ker_proj.1 x.2⟩
          invFun := fun x => ⟨⟨x.1, (Subgroup.mem_inf.1 x.2).1⟩,
            mem_ker_proj.2 (Subgroup.mem_inf.1 x.2).2⟩
          left_inv := fun x => rfl
          right_inv := fun x => rfl }
    obtain ⟨F, hF, hFH⟩ := exists_finset_proj hZ
    have hrange : Nat.card g.range ≤ 4 := by
      let F' : Finset (Multiplicative (F4c × F4c)) := F.image Multiplicative.ofAdd
      have hsub : (g.range : Set (Multiplicative (F4c × F4c))) ⊆ (F' : Set _) := by
        rintro _ ⟨x, rfl⟩
        refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨(x.1.a, x.1.b), hFH x.1 x.2, rfl⟩)
      calc Nat.card g.range = (g.range : Set (Multiplicative (F4c × F4c))).ncard :=
            (Nat.card_coe_set_eq _)
        _ ≤ (F' : Set _).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
        _ = F'.card := Set.ncard_coe_finset _
        _ ≤ F.card := Finset.card_image_le
        _ ≤ 4 := hF
    rw [← h1, hker]
    calc Nat.card ↥(H ⊓ Subgroup.center Tc) * Nat.card g.range
        ≤ Nat.card ↥(H ⊓ Subgroup.center Tc) * 4 := Nat.mul_le_mul_left _ hrange
      _ = 4 * Nat.card ↥(H ⊓ Subgroup.center Tc) := mul_comm _ _
  · have hdvd : Nat.card ↥(H ⊓ Subgroup.center Tc) ∣ 4 := by
      rw [← card_center]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hne : Nat.card ↥(H ⊓ Subgroup.center Tc) ≠ 4 := by
      intro h
      apply hZ
      have : H ⊓ Subgroup.center Tc = Subgroup.center Tc :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [card_center, h])
      rw [← this]
      exact inf_le_left
    obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (by simpa using hdvd : Nat.card ↥(H ⊓ Subgroup.center Tc) ∣ 2 ^ 2)
    have h3 : Nat.card ↥(H ⊓ Subgroup.center Tc) = 1 ∨ Nat.card ↥(H ⊓ Subgroup.center Tc) = 2 ∨
        Nat.card ↥(H ⊓ Subgroup.center Tc) = 4 := by
      interval_cases i <;> rw [hci] <;> norm_num
    omega

theorem inf_center_ne_bot_of_card {H : Subgroup Tc} (hH : 4 < Nat.card H) :
    H ⊓ Subgroup.center Tc ≠ ⊥ := by
  intro hbot
  have hZ : ¬ Subgroup.center Tc ≤ H := by
    intro h
    have : H ⊓ Subgroup.center Tc = Subgroup.center Tc := inf_eq_right.2 h
    rw [hbot] at this
    have h4 := card_center
    rw [← this, Subgroup.card_bot] at h4
    omega
  have := (card_le_of_not_center_le hZ).1
  rw [hbot, Subgroup.card_bot] at this
  omega

end CFSG.OddStandard.ThmC.T
