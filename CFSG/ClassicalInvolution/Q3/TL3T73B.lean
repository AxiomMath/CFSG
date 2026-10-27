module

public import Mathlib.Data.Fintype.Card

public section

namespace CFSG.ClassicalInvolution.Q3.Johnson

open Finset

private theorem inter_subset_or_subset_union {α : Type*} [DecidableEq α] {r : ℕ}
    {a b e : Finset α} (he : e.card = r) (hab : (a ∩ b).card + 1 = r)
    (hea : r ≤ (e ∩ a).card + 1) (heb : r ≤ (e ∩ b).card + 1) :
    a ∩ b ⊆ e ∨ e ⊆ a ∪ b := by
  refine or_iff_not_imp_left.mpr fun h => ?_
  obtain ⟨t, ht, hte⟩ := not_subset.mp h
  have h₁ : (e ∩ (a ∩ b)).card < (a ∩ b).card :=
    card_lt_card ⟨inter_subset_right, fun hs => hte (mem_inter.mp (hs ht)).1⟩
  have h₂ := card_union_add_card_inter (e ∩ a) (e ∩ b)
  rw [← inter_union_distrib_left, ← inter_inter_distrib_left] at h₂
  exact inter_eq_left.mp (eq_of_subset_of_card_le inter_subset_left (by omega))

private theorem star_or_top {κ α : Type*} [DecidableEq α] {r : ℕ} (W : Finset κ)
    (hW : 1 < W.card) (A : κ → Finset α) (hA : ∀ x ∈ W, (A x).card = r)
    (hAA : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → (A x ∩ A y).card + 1 = r) :
    (∃ R : Finset α, R.card + 1 = r ∧ ∀ x ∈ W, R ⊆ A x) ∨
      ∃ Z : Finset α, Z.card = r + 1 ∧ ∀ x ∈ W, A x ⊆ Z := by
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy⟩ := one_lt_card.mp hW
  have hI := hAA x₀ hx₀ y₀ hy₀ hxy
  have hge : ∀ x ∈ W, ∀ y ∈ W, r ≤ (A x ∩ A y).card + 1 := by
    intro x hx y hy
    by_cases hxy : x = y
    · rw [hxy, inter_self, hA y hy]
      omega
    · exact (hAA x hx y hy hxy).ge
  by_cases hstar : ∀ x ∈ W, A x₀ ∩ A y₀ ⊆ A x
  · exact Or.inl ⟨_, hI, hstar⟩
  right
  obtain ⟨d, hd, hdI⟩ : ∃ d ∈ W, ¬A x₀ ∩ A y₀ ⊆ A d := by
    by_contra hcon
    exact hstar fun d hd => Classical.byContradiction fun hd' => hcon ⟨d, hd, hd'⟩
  have hdich : ∀ e ∈ W, A x₀ ∩ A y₀ ⊆ A e ∨ A e ⊆ A x₀ ∪ A y₀ := fun e he =>
    inter_subset_or_subset_union (hA e he) hI (hge e he x₀ hx₀) (hge e he y₀ hy₀)
  have hdZ : A d ⊆ A x₀ ∪ A y₀ := (hdich d hd).resolve_left hdI
  refine ⟨A x₀ ∪ A y₀, ?_, fun e he => ?_⟩
  · have := card_union_add_card_inter (A x₀) (A y₀)
    rw [hA x₀ hx₀, hA y₀ hy₀] at this
    omega
  rcases hdich e he with hIe | hZe
  · by_contra heZ
    have h₁ : A e ∩ (A x₀ ∪ A y₀) = A x₀ ∩ A y₀ := by
      refine (eq_of_subset_of_card_le (subset_inter hIe inter_subset_union) ?_).symm
      have := card_lt_card (⟨inter_subset_left, fun h => heZ fun x hx => (mem_inter.mp (h hx)).2⟩ :
        A e ∩ (A x₀ ∪ A y₀) ⊂ A e)
      rw [hA e he] at this
      omega
    have h₂ : (A e ∩ A d).card < (A x₀ ∩ A y₀).card :=
      calc (A e ∩ A d).card ≤ (A x₀ ∩ A y₀ ∩ A d).card := card_le_card fun x hx => by
            have hx' := mem_inter.mp hx
            have : x ∈ A e ∩ (A x₀ ∪ A y₀) := mem_inter.mpr ⟨hx'.1, hdZ hx'.2⟩
            rw [h₁] at this
            exact mem_inter.mpr ⟨this, hx'.2⟩
        _ < (A x₀ ∩ A y₀).card :=
          card_lt_card ⟨inter_subset_left, fun h => hdI fun x hx => (mem_inter.mp (h hx)).2⟩
    have := hge e he d hd
    omega
  · exact hZe

private theorem exists_eq_erase {α : Type*} [DecidableEq α] {Z V : Finset α} {n : ℕ}
    (hZ : Z.card = n + 1) (hV : V.card = n) (hVZ : V ⊆ Z) : ∃ p ∈ Z, V = Z.erase p := by
  obtain ⟨p, hp⟩ := card_eq_one.mp (show (Z \ V).card = 1 by
    have := card_sdiff_of_subset hVZ
    omega)
  have hpm : p ∈ Z \ V := by rw [hp]; exact mem_singleton_self p
  refine ⟨p, (mem_sdiff.mp hpm).1, ?_⟩
  ext y
  constructor
  · intro hy
    refine mem_erase.mpr ⟨fun h => (mem_sdiff.mp hpm).2 (h ▸ hy), hVZ hy⟩
  · intro hy
    obtain ⟨hne, hyZ⟩ := mem_erase.mp hy
    by_contra hyV
    have : y ∈ Z \ V := mem_sdiff.mpr ⟨hyZ, hyV⟩
    rw [hp, mem_singleton] at this
    exact hne this

variable {j k : ℕ}

private structure Induces (f : Finset (Fin j) → Finset (Fin k)) (T : Finset (Fin j))
    (ι : Fin j → Fin k) : Prop where
  injOn : Set.InjOn ι T
  eq : ∀ α ⊆ T, α.card = 4 → f α = α.image ι

private theorem Induces.mono {f : Finset (Fin j) → Finset (Fin k)} {T T' : Finset (Fin j)}
    {ι : Fin j → Fin k} (h : Induces f T ι) (hT : T' ⊆ T) : Induces f T' ι where
  injOn := h.injOn.mono (coe_subset.mpr hT)
  eq α hα hα4 := h.eq α (hα.trans hT) hα4

private theorem Induces.image_eq {f : Finset (Fin j) → Finset (Fin k)} {T : Finset (Fin j)}
    (hT : 4 ≤ T.card) {ι ι' : Fin j → Fin k} (h : Induces f T ι) (h' : Induces f T ι') :
    T.image ι = T.image ι' := by
  have key : ∀ {a b : Fin j → Fin k}, Induces f T a → Induces f T b →
      T.image a ⊆ T.image b := by
    intro a b ha hb y hy
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hy
    obtain ⟨α, htα, hαT, hα4⟩ := exists_subsuperset_card_eq (singleton_subset_iff.mpr ht)
      (by simp) hT
    have hmem : a t ∈ f α := by
      rw [ha.eq α hαT hα4]
      exact mem_image_of_mem a (singleton_subset_iff.mp htα)
    rw [hb.eq α hαT hα4] at hmem
    exact image_subset_image hαT hmem
  exact Finset.Subset.antisymm (key h h') (key h' h)

private theorem Induces.eq_of_image_eq {f : Finset (Fin j) → Finset (Fin k)}
    (hinj : ∀ α β : Finset (Fin j), α.card = 4 → β.card = 4 → f α = f β → α = β)
    {T T' : Finset (Fin j)} (hT : 4 ≤ T.card) {ι ι' : Fin j → Fin k} (h : Induces f T ι)
    (h' : Induces f T' ι') (hV : T.image ι = T'.image ι') : T = T' := by
  refine eq_of_subset_of_card_le (fun x hx => ?_) ?_
  · obtain ⟨α, hxα, hαT, hα4⟩ := exists_subsuperset_card_eq (singleton_subset_iff.mpr hx)
      (by simp) hT
    have hfα : f α ⊆ T'.image ι' := by
      rw [h.eq α hαT hα4, ← hV]
      exact image_subset_image hαT
    obtain ⟨β, hβT, hβ⟩ := subset_image_iff.mp hfα
    have hβ4 : β.card = 4 := by
      have h1 : (β.image ι').card = β.card :=
        card_image_of_injOn (h'.injOn.mono (coe_subset.mpr hβT))
      have h2 : (α.image ι).card = α.card :=
        card_image_of_injOn (h.injOn.mono (coe_subset.mpr hαT))
      rw [hβ, h.eq α hαT hα4] at h1
      omega
    have hβα : β = α := hinj β α hβ4 hα4 (by rw [h'.eq β hβT hβ4, hβ, h.eq α hαT hα4])
    exact hβT (by rw [hβα]; exact singleton_subset_iff.mp hxα)
  · exact le_of_eq (calc T'.card = (T'.image ι').card := (card_image_of_injOn h'.injOn).symm
      _ = (T.image ι).card := by rw [hV]
      _ = T.card := card_image_of_injOn h.injOn)

private theorem exists_induces_five {f : Finset (Fin j) → Finset (Fin k)}
    (hf4 : ∀ α : Finset (Fin j), α.card = 4 → (f α).card = 4)
    (hinj : ∀ α β : Finset (Fin j), α.card = 4 → β.card = 4 → f α = f β → α = β)
    (htop : ∀ S : Finset (Fin j), S.card = 5 →
      ∃ U : Finset (Fin k), U.card = 5 ∧ ∀ α ⊆ S, α.card = 4 → f α ⊆ U)
    (W : Finset (Fin j)) (hW : W.card = 5) : ∃ ι : Fin j → Fin k, Induces f W ι := by
  obtain ⟨U, hU, hfU⟩ := htop W hW
  have hWx : ∀ x ∈ W, (W.erase x).card = 4 := fun x hx => by
    have := card_erase_of_mem hx
    omega
  have hex : ∀ x ∈ W, ∃ p ∈ U, f (W.erase x) = U.erase p := fun x hx =>
    exists_eq_erase hU (hf4 _ (hWx x hx)) (hfU _ (erase_subset x W) (hWx x hx))
  obtain ⟨x₀, hx₀⟩ : W.Nonempty := card_pos.mp (by omega)
  have : Nonempty (Fin k) := ⟨(hex x₀ hx₀).choose⟩
  choose! h hhU hfh using hex
  have hinjh : Set.InjOn h W := by
    intro x hx y hy hxy
    have hx' := mem_coe.mp hx
    have hy' := mem_coe.mp hy
    by_contra hne
    have h1 : W.erase x = W.erase y :=
      hinj _ _ (hWx x hx') (hWx y hy') (by rw [hfh x hx', hfh y hy', hxy])
    have h2 : y ∈ W.erase x := mem_erase.mpr ⟨fun h => hne h.symm, hy'⟩
    rw [h1] at h2
    exact (mem_erase.mp h2).1 rfl
  refine ⟨h, hinjh, fun α hαW hα4 => ?_⟩
  obtain ⟨x, hx⟩ := card_eq_one.mp (show (W \ α).card = 1 by
    have := card_sdiff_of_subset hαW
    omega)
  have hxm : x ∈ W \ α := by rw [hx]; exact mem_singleton_self x
  obtain ⟨hxW, hxα⟩ := mem_sdiff.mp hxm
  have hαx : α = W.erase x := eq_of_subset_of_card_le
    (fun a ha => mem_erase.mpr ⟨fun hax => hxα (by rw [← hax]; exact ha), hαW ha⟩)
    (by rw [hWx x hxW, hα4])
  rw [hαx, hfh x hxW]
  refine (eq_of_subset_of_card_le ?_ ?_).symm
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hy
    obtain ⟨hax, haW⟩ := mem_erase.mp ha
    exact mem_erase.mpr ⟨fun hh => hax (hinjh (mem_coe.mpr haW) (mem_coe.mpr hxW) hh),
      hhU a haW⟩
  · have h1 := card_erase_of_mem (hhU x hxW)
    have h2 : ((W.erase x).image h).card = (W.erase x).card :=
      card_image_of_injOn (hinjh.mono (coe_subset.mpr (erase_subset x W)))
    have h3 := hWx x hxW
    omega

private theorem exists_induces_succ {f : Finset (Fin j) → Finset (Fin k)}
    (hf4 : ∀ α : Finset (Fin j), α.card = 4 → (f α).card = 4)
    (hinj : ∀ α β : Finset (Fin j), α.card = 4 → β.card = 4 → f α = f β → α = β) {m : ℕ}
    (hm : 5 ≤ m) (hP : ∀ T : Finset (Fin j), T.card = m → ∃ ι : Fin j → Fin k, Induces f T ι)
    (W : Finset (Fin j)) (hW : W.card = m + 1) : ∃ ι : Fin j → Fin k, Induces f W ι := by
  have hcardE : ∀ x ∈ W, (W.erase x).card = m := fun x hx => by
    have := card_erase_of_mem hx
    omega
  have hex : ∀ x ∈ W, ∃ ι : Fin j → Fin k, Induces f (W.erase x) ι := fun x hx =>
    hP _ (hcardE x hx)
  obtain ⟨x₀, hx₀⟩ : W.Nonempty := card_pos.mp (by omega)
  have : Nonempty (Fin k) := ⟨(hex x₀ hx₀).choose x₀⟩
  choose! ι hι using hex
  obtain ⟨V, hV⟩ : ∃ V : Fin j → Finset (Fin k), ∀ x, V x = (W.erase x).image (ι x) :=
    ⟨fun x => (W.erase x).image (ι x), fun _ => rfl⟩
  have hVcard : ∀ x ∈ W, (V x).card = m := fun x hx => by
    rw [hV, card_image_of_injOn (hι x hx).injOn, hcardE x hx]
  have hT1 : ∀ x y : Fin j, (W.erase x).erase y ⊆ W.erase x := fun x y => erase_subset _ _
  have hT2 : ∀ x y : Fin j, (W.erase x).erase y ⊆ W.erase y := fun x y z hz =>
    mem_erase.mpr ⟨(mem_erase.mp hz).1, mem_of_mem_erase (mem_of_mem_erase hz)⟩
  have hTcard : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → ((W.erase x).erase y).card = m - 1 := by
    intro x hx y hy hxy
    have := card_erase_of_mem (mem_erase.mpr ⟨hxy.symm, hy⟩)
    rw [hcardE x hx] at this
    exact this
  have hagree : ∀ x ∈ W, ∀ y ∈ W, x ≠ y →
      ((W.erase x).erase y).image (ι x) = ((W.erase x).erase y).image (ι y) := by
    intro x hx y hy hxy
    have := hTcard x hx y hy hxy
    exact Induces.image_eq (by omega) (Induces.mono (hι x hx) (hT1 x y))
      (Induces.mono (hι y hy) (hT2 x y))
  have hTV : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → ((W.erase x).erase y).image (ι x) ⊆ V x ∩ V y := by
    intro x hx y hy hxy
    refine subset_inter ?_ ?_
    · rw [hV]
      exact image_subset_image (hT1 x y)
    · rw [hagree x hx y hy hxy, hV]
      exact image_subset_image (hT2 x y)
  have hVne : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → V x ≠ V y := by
    intro x hx y hy hxy hVxy
    have := hcardE x hx
    have h1 := Induces.eq_of_image_eq hinj (by omega) (hι x hx) (hι y hy)
      ((hV x).symm.trans (hVxy.trans (hV y)))
    have h2 : y ∈ W.erase x := mem_erase.mpr ⟨fun h => hxy h.symm, hy⟩
    rw [h1] at h2
    exact (mem_erase.mp h2).1 rfl
  have hVV : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → (V x ∩ V y).card + 1 = m := by
    intro x hx y hy hxy
    have h1 := card_le_card (hTV x hx y hy hxy)
    rw [card_image_of_injOn (Induces.mono (hι x hx) (hT1 x y)).injOn,
      hTcard x hx y hy hxy] at h1
    have h2 : (V x ∩ V y).card < m := by
      have hss : V x ∩ V y ⊂ V x := ⟨inter_subset_left, fun h => hVne x hx y hy hxy
        (eq_of_subset_of_card_le (fun z hz => (mem_inter.mp (h hz)).2)
          (le_of_eq ((hVcard y hy).trans (hVcard x hx).symm)))⟩
      have := card_lt_card hss
      rw [hVcard x hx] at this
      exact this
    omega
  have hTeq : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → ((W.erase x).erase y).image (ι x) = V x ∩ V y := by
    intro x hx y hy hxy
    refine eq_of_subset_of_card_le (hTV x hx y hy hxy) ?_
    have h1 : (((W.erase x).erase y).image (ι x)).card = ((W.erase x).erase y).card :=
      card_image_of_injOn (Induces.mono (hι x hx) (hT1 x y)).injOn
    have h2 := hTcard x hx y hy hxy
    have h3 := hVV x hx y hy hxy
    omega
  rcases star_or_top W (by omega) V hVcard hVV with ⟨R, hR, hRsub⟩ | ⟨Z, hZ, hZsub⟩
  ·
    exfalso
    obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := two_lt_card.mp (show 2 < W.card by omega)
    have hRV : ∀ w ∈ W, w ≠ x → ((W.erase x).erase w).image (ι x) = R := by
      intro w hw hwx
      have hsub : R ⊆ V x ∩ V w := subset_inter (hRsub x hx) (hRsub w hw)
      have h3 := hVV x hx w hw hwx.symm
      have := eq_of_subset_of_card_le hsub (by omega)
      exact (hTeq x hx w hw hwx.symm).trans this.symm
    have hzT : z ∈ (W.erase x).erase y := mem_erase.mpr ⟨hyz.symm, mem_erase.mpr ⟨hxz.symm, hz⟩⟩
    have himg : ι x z ∈ ((W.erase x).erase z).image (ι x) := by
      rw [hRV z hz hxz.symm, ← hRV y hy hxy.symm]
      exact mem_image_of_mem _ hzT
    obtain ⟨w, hw, hwz⟩ := mem_image.mp himg
    have hzW : z ∈ W.erase x := mem_erase.mpr ⟨hxz.symm, hz⟩
    exact (mem_erase.mp hw).1
      ((hι x hx).injOn (mem_coe.mpr (mem_of_mem_erase hw)) (mem_coe.mpr hzW) hwz)
  ·
    have hZV : ∀ x ∈ W, ∃ p ∈ Z, V x = Z.erase p := fun x hx =>
      exists_eq_erase hZ (hVcard x hx) (hZsub x hx)
    choose! p hpZ hVp using hZV
    have hpinj : Set.InjOn p W := by
      intro x hx y hy hxy
      have hx' := mem_coe.mp hx
      have hy' := mem_coe.mp hy
      by_contra hne
      exact hVne x hx' y hy' hne (by rw [hVp x hx', hVp y hy', hxy])
    refine ⟨p, hpinj, fun α hαW hα4 => ?_⟩
    have hWα : (W \ α).card = m + 1 - 4 := by
      have := card_sdiff_of_subset hαW
      omega
    have hmem : ∀ x ∈ W \ α, f α ⊆ Z.erase (p x) := by
      intro x hx
      obtain ⟨hxW, hxα⟩ := mem_sdiff.mp hx
      have hαx : α ⊆ W.erase x :=
        fun a ha => mem_erase.mpr ⟨fun h => hxα (by rw [← h]; exact ha), hαW ha⟩
      rw [(hι x hxW).eq α hαx hα4, ← hVp x hxW, hV]
      exact image_subset_image hαx
    obtain ⟨x₁, hx₁⟩ : (W \ α).Nonempty := card_pos.mp (by omega)
    have himgZ : (W \ α).image p ⊆ Z := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
      exact hpZ x (mem_sdiff.mp hx).1
    have hQcard : (Z \ (W \ α).image p).card = 4 := by
      have h1 := card_sdiff_of_subset himgZ
      have h2 : ((W \ α).image p).card = (W \ α).card :=
        card_image_of_injOn (hpinj.mono (coe_subset.mpr sdiff_subset))
      omega
    have hfsub : f α ⊆ Z \ (W \ α).image p := by
      intro y hy
      refine mem_sdiff.mpr ⟨mem_of_mem_erase (hmem x₁ hx₁ hy), fun hy' => ?_⟩
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hy'
      exact (mem_erase.mp (hmem x hx hy)).1 rfl
    have hαsub : α.image p ⊆ Z \ (W \ α).image p := by
      intro y hy
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hy
      refine mem_sdiff.mpr ⟨hpZ a (hαW ha), fun hy' => ?_⟩
      obtain ⟨b, hb, hba⟩ := mem_image.mp hy'
      obtain ⟨hbW, hbα⟩ := mem_sdiff.mp hb
      have hba' : b = a := hpinj (mem_coe.mpr hbW) (mem_coe.mpr (hαW ha)) hba
      exact hbα (by rw [hba']; exact ha)
    have hαcard : (α.image p).card = 4 := by
      rw [card_image_of_injOn (hpinj.mono (coe_subset.mpr hαW)), hα4]
    have e1 : f α = Z \ (W \ α).image p :=
      eq_of_subset_of_card_le hfsub (by have := hf4 α hα4; omega)
    have e2 : α.image p = Z \ (W \ α).image p :=
      eq_of_subset_of_card_le hαsub (by omega)
    rw [e1, e2]

private theorem exists_induces {f : Finset (Fin j) → Finset (Fin k)}
    (hf4 : ∀ α : Finset (Fin j), α.card = 4 → (f α).card = 4)
    (hinj : ∀ α β : Finset (Fin j), α.card = 4 → β.card = 4 → f α = f β → α = β)
    (htop : ∀ S : Finset (Fin j), S.card = 5 →
      ∃ U : Finset (Fin k), U.card = 5 ∧ ∀ α ⊆ S, α.card = 4 → f α ⊆ U) {m : ℕ} (hm : 5 ≤ m) :
    ∀ T : Finset (Fin j), T.card = m → ∃ ι : Fin j → Fin k, Induces f T ι := by
  induction m, hm using Nat.le_induction with
  | base => exact fun T hT => exists_induces_five hf4 hinj htop T hT
  | succ m hm ih => exact fun T hT => exists_induces_succ hf4 hinj hm ih T hT

theorem exists_emb_of_tops {j k : ℕ} (hj5 : 5 ≤ j) (hj7 : j ≤ 7) (hk : k ≤ j + 2)
    (f : Finset (Fin j) → Finset (Fin k))
    (hf4 : ∀ α : Finset (Fin j), α.card = 4 → (f α).card = 4)
    (hinj : ∀ α β : Finset (Fin j), α.card = 4 → β.card = 4 → f α = f β → α = β)
    (htop : ∀ S : Finset (Fin j), S.card = 5 →
      ∃ U : Finset (Fin k), U.card = 5 ∧ ∀ α ⊆ S, α.card = 4 → f α ⊆ U) :
    ∃ ι : Fin j ↪ Fin k, ∀ α : Finset (Fin j), α.card = 4 → f α = α.map ι := by
  obtain ⟨ι, hι⟩ := exists_induces hf4 hinj htop hj5 Finset.univ (by simp)
  have hι' : Function.Injective ι := fun a b hab =>
    hι.injOn (mem_coe.mpr (mem_univ a)) (mem_coe.mpr (mem_univ b)) hab
  refine ⟨⟨ι, hι'⟩, fun α hα => ?_⟩
  rw [hι.eq α (subset_univ α) hα]
  exact (map_eq_image (⟨ι, hι'⟩ : Fin j ↪ Fin k) α).symm

end CFSG.ClassicalInvolution.Q3.Johnson
