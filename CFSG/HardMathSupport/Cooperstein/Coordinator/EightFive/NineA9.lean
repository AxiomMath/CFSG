module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.NineCore
public import CFSG.Quasithin.Background.Harris.Ln2.PermRank

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm MulAction

variable {V : Type} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)}
  {ψ : ↥H →* Perm (Fin 9)}

theorem a9 (hV : ∀ v : V, v ^ 2 = 1) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin 9) ≤ ψ.range)
    (h3 : ∀ x : ↥H, (ψ x).IsThreeCycle → fixV (Subgroup.zpowers (x : MulAut V)) = ⊥)
    {B : Subgroup (MulAut V)} (hBH : B ≤ H) (hB : B ≠ ⊥) (hel : IsElemAbelian2 B) :
    Nat.card B * Nat.card (fixV B) < Nat.card V := by
  by_contra hcon
  push Not at hcon
  set E : Subgroup (Perm (Fin 9)) := (B.subgroupOf H).map ψ with hE_def
  have hcardE : Nat.card E = Nat.card B := by
    rw [hE_def, Subgroup.card_map_of_injective hψ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv
  have hmemE : ∀ h : ↥H, (h : MulAut V) ∈ B → ψ h ∈ E := fun h hh =>
    ⟨h, Subgroup.mem_subgroupOf.2 hh, rfl⟩
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (hel.1 _ ha _ hb))
  have hE2 : ∀ a ∈ E, a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    exact apply_mul_apply_eq_one (hel.2 _ ha)
  have hB16 : Nat.card B ≤ 16 := by
    have h := CFSG.Quasithin.G11.Harris.Ln2.card_le_of_elemAbelian_perm hEc hE2
    rw [hcardE, Fintype.card_fin] at h
    exact h
  have hP : IsPGroup 2 E := fun g =>
    ⟨1, Subtype.ext (by rw [Subgroup.coe_pow, pow_one, pow_two, Subgroup.coe_one]; exact hE2 _ g.2)⟩
  obtain ⟨r, hr⟩ : ∃ r : Fin 9, ∀ e ∈ E, e r = r := by
    by_contra hne
    push Not at hne
    have hempty : fixedPoints E (Fin 9) = ∅ := by
      ext q
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hq
      obtain ⟨e, he, heq⟩ := hne q
      exact heq (hq ⟨e, he⟩)
    have hmod := hP.card_modEq_card_fixedPoints (Fin 9)
    rw [hempty, Nat.card_eq_fintype_card, Fintype.card_fin] at hmod
    simp [Nat.ModEq] at hmod
  obtain ⟨⟨t, htB⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB
  let th : ↥H := ⟨t, hBH htB⟩
  have hψt : ψ th ≠ 1 := by
    intro h
    apply ht1
    have h1 : th = 1 := hψ (h.trans (map_one ψ).symm)
    have h2 : (th : MulAut V) = 1 := congrArg Subtype.val h1
    exact Subtype.ext h2
  obtain ⟨p, hp⟩ : ∃ p, ψ th p ≠ p := by
    by_contra hcon'
    push Not at hcon'
    exact hψt (Equiv.ext hcon')
  have htr : ψ th r = r := hr _ (hmemE th htB)
  have hpr : p ≠ r := by
    rintro rfl
    exact hp htr
  have ht := card_fixV_sq_of_apply_ne hV hψ hA h3 (s := th) (hel.2 _ htB) hp htr
  have hV8 := two_pow_eight_le_card hV le_rfl hψ hA h3
  have hB16' : 16 ≤ Nat.card B := by
    set c := Nat.card (fixV (Subgroup.zpowers (th : MulAut V)))
    have hle : Nat.card (fixV B) ≤ c := Subgroup.card_le_of_le (fixV_zpowers_le htB)
    have hc16 : 16 ≤ c := by
      by_contra h
      have h1 : c ^ 2 ≤ 15 ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    have h1 : c * c ≤ Nat.card B * c :=
      calc c * c = Nat.card V := by rw [← ht]; ring
        _ ≤ Nat.card B * Nat.card (fixV B) := hcon
        _ ≤ Nat.card B * c := Nat.mul_le_mul_left _ hle
    have h2 : c ≤ Nat.card B := Nat.le_of_mul_le_mul_right h1 (by omega)
    omega
  have horb : (orbit E p).ncard ≤ 8 := by
    have hsub : orbit E p ⊆ ({r}ᶜ : Set (Fin 9)) := by
      rintro _ ⟨e, rfl⟩ he
      apply hpr
      have h1 : (e : Perm (Fin 9)) p = r := he
      exact (e : Perm (Fin 9)).injective (h1.trans (hr _ e.2).symm)
    calc (orbit E p).ncard ≤ ({r}ᶜ : Set (Fin 9)).ncard := Set.ncard_le_ncard hsub
      _ = 8 := by rw [Set.ncard_compl, Set.ncard_singleton, Nat.card_eq_fintype_card,
        Fintype.card_fin]
  have hstab : stabilizer E p ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot]
    have h1 := Subgroup.card_mul_index (stabilizer E p)
    rw [index_stabilizer, hcardE] at h1
    by_contra h
    have h2 : Nat.card (stabilizer E p) ≤ 1 := by omega
    have h3 : Nat.card (stabilizer E p) * (orbit E p).ncard ≤ 1 * 8 := Nat.mul_le_mul h2 horb
    omega
  obtain ⟨⟨⟨e, he⟩, hep⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hstab
  obtain ⟨bh, hbB, rfl⟩ := he
  have hbp : ψ bh p = p := hep
  have hbr : ψ bh r = r := hr _ ⟨bh, hbB, rfl⟩
  have hb1 : bh ≠ 1 := by
    rintro rfl
    apply he1
    ext q
    simp
  exact false_of_core3 hV le_rfl hψ hA h3 hel hB16 hcon (t := th) (b := bh) htB
    (Subgroup.mem_subgroupOf.1 hbB) hb1 htr hp hbp hbr

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
