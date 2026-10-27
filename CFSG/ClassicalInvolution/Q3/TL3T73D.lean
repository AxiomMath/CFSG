module

public import CFSG.ClassicalInvolution.Q3.TL3T73
public import CFSG.ClassicalInvolution.Q3.TL4AECover
public import CFSG.ClassicalInvolution.Q3.TL4AECoverG

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

theorem exists_emb_of_tops' (hj5 : 5 ≤ j) (f : Finset (Fin j) → Finset (Fin k))
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

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE

private theorem kleinOn_le_alternatingGroup {n : ℕ} (A : Finset (Fin n)) :
    kleinOn A ≤ alternatingGroup (Fin n) := fun _ hσ =>
  Equiv.Perm.mem_alternatingGroup.mpr (sign_of_mem_kleinOn hσ)

private theorem exists_emb_core {j k : ℕ} (hj5 : 5 ≤ j)
    (ρ : alternatingGroup (Fin j) →* Equiv.Perm (Fin k)) (hρ : Function.Injective ρ)
    (f : Finset (Fin j) → Finset (Fin k))
    (hf4 : ∀ α : Finset (Fin j), α.card = 4 → (f α).card = 4)
    (hK : ∀ α : Finset (Fin j), α.card = 4 →
      ((kleinOn α).subgroupOf (alternatingGroup (Fin j))).map ρ = kleinOn (f α)) :
    ∃ ι : Fin j ↪ Fin k, ∀ α : Finset (Fin j), α.card = 4 → f α = α.map ι := by
  have hfwd : ∀ α : Finset (Fin j), α.card = 4 → ∀ x : alternatingGroup (Fin j),
      (x : Equiv.Perm (Fin j)) ∈ kleinOn α → ρ x ∈ kleinOn (f α) := by
    intro α hα x hx
    rw [← hK α hα]
    exact Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.mpr hx)
  have hbwd : ∀ α : Finset (Fin j), α.card = 4 → ∀ y ∈ kleinOn (f α),
      ∃ x : alternatingGroup (Fin j), (x : Equiv.Perm (Fin j)) ∈ kleinOn α ∧ ρ x = y := by
    intro α hα y hy
    rw [← hK α hα] at hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  have hord : ∀ x : alternatingGroup (Fin j), orderOf (ρ x) = orderOf (x : Equiv.Perm (Fin j)) :=
    fun x => by rw [orderOf_injective ρ hρ x, Subgroup.orderOf_coe]
  have hfinj : ∀ α β : Finset (Fin j), α.card = 4 → β.card = 4 → f α = f β → α = β := by
    intro α β hα hβ h
    have h1 : (kleinOn α).subgroupOf (alternatingGroup (Fin j)) =
        (kleinOn β).subgroupOf (alternatingGroup (Fin j)) :=
      Subgroup.map_injective hρ (by rw [hK α hα, hK β hβ, h])
    rw [Subgroup.subgroupOf_inj, inf_of_le_left (kleinOn_le_alternatingGroup α),
      inf_of_le_left (kleinOn_le_alternatingGroup β)] at h1
    exact eq_of_kleinOn_eq hα hβ h1
  have hD1 : ∀ α β : Finset (Fin j), α.card = 4 → β.card = 4 →
      ((α ∩ β).card = 3 ↔ (f α ∩ f β).card = 3) := by
    intro α β hα hβ
    rw [← exists_five_dvd_orderOf_iff hα hβ,
      ← exists_five_dvd_orderOf_iff (hf4 α hα) (hf4 β hβ)]
    constructor
    · rintro ⟨x, hx, y, hy, h5⟩
      have hxa : x ∈ alternatingGroup (Fin j) :=
        Equiv.Perm.mem_alternatingGroup.mpr (sign_of_mem_kleinOn hx)
      have hya : y ∈ alternatingGroup (Fin j) :=
        Equiv.Perm.mem_alternatingGroup.mpr (sign_of_mem_kleinOn hy)
      refine ⟨ρ ⟨x, hxa⟩, hfwd α hα ⟨x, hxa⟩ hx, ρ ⟨y, hya⟩, hfwd β hβ ⟨y, hya⟩ hy, ?_⟩
      rw [← map_mul, hord]
      exact h5
    · rintro ⟨x', hx', y', hy', h5⟩
      obtain ⟨x, hx, rfl⟩ := hbwd α hα x' hx'
      obtain ⟨y, hy, rfl⟩ := hbwd β hβ y' hy'
      refine ⟨x, hx, y, hy, ?_⟩
      rw [← map_mul, hord] at h5
      exact h5
  have htop : ∀ S : Finset (Fin j), S.card = 5 →
      ∃ U : Finset (Fin k), U.card = 5 ∧ ∀ α ⊆ S, α.card = 4 → f α ⊆ U := by
    intro S hS
    have hSe : ∀ x ∈ S, (S.erase x).card = 4 := fun x hx => by
      rw [Finset.card_erase_of_mem hx, hS]
    have herase : ∀ x ∈ S, ∀ y ∈ S, S.erase x = S.erase y → x = y := by
      intro x hx y hy h
      by_contra hne
      have h1 : x ∈ S.erase y := Finset.mem_erase.mpr ⟨hne, hx⟩
      rw [← h] at h1
      exact (Finset.mem_erase.mp h1).1 rfl
    have hAA : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
        (f (S.erase x) ∩ f (S.erase y)).card + 1 = 4 := by
      intro x hx y hy hxy
      have h3 : (S.erase x ∩ S.erase y).card = 3 := by
        have e : S.erase x ∩ S.erase y = (S.erase x).erase y := by
          ext z
          simp only [Finset.mem_inter, Finset.mem_erase]
          tauto
        have h4 := Finset.card_erase_of_mem
          (Finset.mem_erase.mpr ⟨hxy.symm, hy⟩ : y ∈ S.erase x)
        have h5 := hSe x hx
        rw [e]
        omega
      have := (hD1 _ _ (hSe x hx) (hSe y hy)).mp h3
      omega
    rcases Johnson.star_or_top S (by omega) (fun x => f (S.erase x))
      (fun x hx => hf4 _ (hSe x hx)) hAA with ⟨R, hR, hRsub⟩ | ⟨Z, hZ, hZsub⟩
    ·
      exfalso
      obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ :=
        Finset.two_lt_card.mp (show 2 < S.card by omega)
      have hR3 : R.card = 3 := by omega
      have hins : ∀ x ∈ S, ∃ y ∉ R, insert y R = f (S.erase x) := fun x hx =>
        Finset.exists_eq_insert_iff.mpr ⟨hRsub x hx, by rw [hf4 _ (hSe x hx)]; exact hR⟩
      obtain ⟨xa, hxa, hea⟩ := hins a ha
      obtain ⟨xb, hxb, heb⟩ := hins b hb
      obtain ⟨xc, hxc, hec⟩ := hins c hc
      have hne : ∀ {x y : Fin j} {u v : Fin k}, x ∈ S → y ∈ S → x ≠ y →
          insert u R = f (S.erase x) → insert v R = f (S.erase y) → u ≠ v := by
        intro x y u v hx hy hxy hu hv huv
        subst huv
        exact hxy (herase x hx y hy (hfinj _ _ (hSe x hx) (hSe y hy) (hu.symm.trans hv)))
      obtain ⟨x, hx, y, hy, w, hw, h4⟩ := exists_orderOf_eq_four_star hR3 hxa hxb hxc
        (hne ha hb hab hea heb) (hne ha hc hac hea hec) (hne hb hc hbc heb hec)
      rw [hea] at hx
      rw [heb] at hy
      rw [hec] at hw
      obtain ⟨x', hx', rfl⟩ := hbwd _ (hSe a ha) x hx
      obtain ⟨y', hy', rfl⟩ := hbwd _ (hSe b hb) y hy
      obtain ⟨w', hw', rfl⟩ := hbwd _ (hSe c hc) w hw
      rw [← map_mul, ← map_mul, hord] at h4
      have hsign : Equiv.Perm.sign ((x' * y' * w' : alternatingGroup (Fin j)) :
          Equiv.Perm (Fin j)) = 1 :=
        Equiv.Perm.mem_alternatingGroup.mp (x' * y' * w').2
      have hfix : ∀ z ∉ S, ((x' * y' * w' : alternatingGroup (Fin j)) :
          Equiv.Perm (Fin j)) z = z := by
        intro z hz
        have hz1 : z ∉ S.erase a := fun h => hz (Finset.mem_of_mem_erase h)
        have hz2 : z ∉ S.erase b := fun h => hz (Finset.mem_of_mem_erase h)
        have hz3 : z ∉ S.erase c := fun h => hz (Finset.mem_of_mem_erase h)
        show (x' : Equiv.Perm (Fin j)) ((y' : Equiv.Perm (Fin j)) ((w' : Equiv.Perm (Fin j)) z)) = z
        rw [fix_of_mem_kleinOn hw' hz3, fix_of_mem_kleinOn hy' hz2, fix_of_mem_kleinOn hx' hz1]
      rcases orderOf_of_support_five hsign hS hfix with h | h | h | h <;> omega
    ·
      refine ⟨Z, hZ, fun α hαS hα4 => ?_⟩
      obtain ⟨x, hx, rfl⟩ := Johnson.exists_eq_erase (n := 4) (by omega) hα4 hαS
      exact hZsub x hx
  exact Johnson.exists_emb_of_tops' hj5 f hf4 hfinj htop

section Parts

variable {G : Type} [Group G] {P P' : Set (Subgroup G)}

private noncomputable def smallPsiHom (hle : pSpan P ≤ pSpan P') {k : ℕ} (I' : AEIdent P' k) :
    ↥(pSpan P) →* Equiv.Perm (Fin k) :=
  (permQ k).comp (I'.φ.comp (Subgroup.inclusion hle))

private theorem map_inclusion_subgroupOf {H H' : Subgroup G} (hle : H ≤ H') {M : Subgroup G}
    (hM : M ≤ H) : (M.subgroupOf H).map (Subgroup.inclusion hle) = M.subgroupOf H' := by
  ext ⟨y, hy'⟩
  constructor
  · rintro ⟨⟨z, hz⟩, hzM, he⟩
    have hzy : z = y := congrArg Subtype.val he
    subst hzy
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hzM)
  · intro hyM
    have hyM' : y ∈ M := Subgroup.mem_subgroupOf.mp hyM
    exact ⟨⟨y, hM hyM'⟩, Subgroup.mem_subgroupOf.mpr hyM', rfl⟩

private theorem map_smallPsiHom_eq (hle : pSpan P ≤ pSpan P') {k : ℕ} (I' : AEIdent P' k)
    {M : Subgroup G} (hM : M ≤ pSpan P) {β : Finset (Fin k)} {hβ : β.card = 4} {d : Bool}
    (hlab : (M.subgroupOf (pSpan P')).map I'.φ = memBar β hβ d) :
    (M.subgroupOf (pSpan P)).map (smallPsiHom hle I') = kleinOn β := by
  rw [smallPsiHom, ← Subgroup.map_map, ← Subgroup.map_map, map_inclusion_subgroupOf hle hM, hlab,
    map_permQ_memBar]

private theorem map_permHom_eq {k : ℕ} (I : AEIdent P k) {M : Subgroup G} {α : Finset (Fin k)}
    {hα : α.card = 4} {b : Bool} (hlab : (M.subgroupOf (pSpan P)).map I.φ = memBar α hα b) :
    (M.subgroupOf (pSpan P)).map (TL4.AECov.permHom I) =
      (kleinOn α).subgroupOf (alternatingGroup (Fin k)) := by
  have hcomp : (alternatingGroup (Fin k)).subtype.comp (TL4.AECov.permHom I) =
      (permQ k).comp I.φ := MonoidHom.ext fun x => rfl
  refine Subgroup.map_injective (alternatingGroup (Fin k)).subtype_injective ?_
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hlab, map_permQ_memBar,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left (kleinOn_le_alternatingGroup α)]

private theorem ker_permHom_le_zSpan' [Finite G] {k : ℕ} (I : AEIdent P k) (hk : 5 ≤ k)
    (hH : TL4.AECoverHyp I) : (TL4.AECov.permHom I).ker ≤ TL4.AECov.zSpan P := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hcomm : ∀ L ∈ P, ∀ L' ∈ P, ∀ u u' : G, IsUniqueInvolution L u →
      IsUniqueInvolution L' u' → u * u' = u' * u := fun L hL L' hL' u u' hu hu' =>
    TL4.AECov.comm_of_isUniqueInvolution I hk hH.card hH.conj_mem hH.label_inj hH.twin_z hL hL'
      hu hu'
  exact TL4.AECov.ker_permHom_le_zSpan I (by omega) hH.card hH.conj_mem hH.label_inj hH.ker_two
    (TL4.AECov.zSpan_normal hH.conj_mem) (TL4.AECov.zSpan_elem hcomm)

private theorem zSpan_le_ker_smallPsiHom [Finite G] (hPP : P ⊆ P') (hle : pSpan P ≤ pSpan P')
    {k : ℕ} (hk : 5 ≤ k) (I' : AEIdent P' k) (h8 : ∀ L ∈ P, Nat.card ↥L = 8) :
    TL4.AECov.zSpan P ≤ (smallPsiHom hle I').ker := by
  rw [TL4.AECov.zSpan, Subgroup.closure_le]
  rintro x ⟨L, hL, hxL⟩
  obtain ⟨β, h', b', hlab'⟩ := I'.label L (hPP hL)
  have hz := I'.map_eq_zBar hk (hPP hL) (h8 L hL) hlab' hxL
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  show permQ k (I'.φ ⟨(x : G), hle x.2⟩) = 1
  rw [show (⟨(x : G), hle x.2⟩ : ↥(pSpan P')) = ⟨(x : G), le_pSpan (hPP hL) hxL.mem⟩ from rfl, hz,
    zBar, permQ_mkQ, zOf_perm]

end Parts

variable {G : Type} [Group G]

theorem exists_emb_of_aeIdent_small' [Finite G] {P P' : Set (Subgroup G)} (hPP : P ⊆ P') {j k : ℕ}
    (hj5 : 5 ≤ j) (hk5 : 5 ≤ k) (I : AEIdent P j) (I' : AEIdent P' k)
    (hH : TL4.AECoverHyp I) (hzL : ∀ L ∈ P, ∃ u, IsUniqueInvolution L u) :
    ∃ ι : Fin j ↪ Fin k, ∀ L ∈ P, ∀ (α : Finset (Fin j)) (hα : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan P)).map I.φ = memBar α hα b →
      ∃ (hα' : (α.map ι).card = 4) (b' : Bool),
        (L.subgroupOf (pSpan P')).map I'.φ = memBar (α.map ι) hα' b' := by
  have hle : pSpan P ≤ pSpan P' := pSpan_le fun L hL => le_pSpan (hPP hL)
  have hker : (TL4.AECov.permHom I).ker ≤ (smallPsiHom hle I').ker :=
    (ker_permHom_le_zSpan' I hj5 hH).trans (zSpan_le_ker_smallPsiHom hPP hle hk5 I' hH.card)
  obtain ⟨ρ, hρp⟩ : ∃ ρ : alternatingGroup (Fin j) →* Equiv.Perm (Fin k),
      ∀ x, ρ (TL4.AECov.permHom I x) = smallPsiHom hle I' x :=
    ⟨(TL4.AECov.permHom I).liftOfSurjective (TL4.AECov.permHom_surjective I)
      ⟨smallPsiHom hle I', hker⟩, fun x => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x⟩
  have hKey : ∀ M ∈ P, ∀ (α : Finset (Fin j)) (hα : α.card = 4) (b : Bool)
      (β : Finset (Fin k)) (hβ : β.card = 4) (d : Bool),
      (M.subgroupOf (pSpan P)).map I.φ = memBar α hα b →
      (M.subgroupOf (pSpan P')).map I'.φ = memBar β hβ d →
      ((kleinOn α).subgroupOf (alternatingGroup (Fin j))).map ρ = kleinOn β := by
    intro M hM α hα b β hβ d hlab hlab'
    rw [← map_permHom_eq I hlab, Subgroup.map_map, ← map_smallPsiHom_eq hle I' (le_pSpan hM) hlab']
    congr 1
    exact MonoidHom.ext hρp
  have hsimple : IsSimpleGroup (alternatingGroup (Fin j)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hj5)
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases ρ.normal_ker.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨α₀, -, hα₀⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin j)))
        (n := 4) (by rw [Finset.card_univ, Fintype.card_fin]; omega)
      obtain ⟨M₀, hM₀, hlab₀⟩ := I.label_surj α₀ hα₀ true
      obtain ⟨β₀, hβ₀, d₀, hlab₀'⟩ := I'.label M₀ (hPP hM₀)
      have h1 := hKey M₀ hM₀ α₀ hα₀ true β₀ hβ₀ d₀ hlab₀ hlab₀'
      have hne : kleinOn β₀ ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, natCard_kleinOn hβ₀]
        norm_num
      refine hne ?_
      rw [← h1, eq_bot_iff]
      rintro _ ⟨x, -, rfl⟩
      rw [Subgroup.mem_bot, ← MonoidHom.mem_ker, h]
      exact Subgroup.mem_top x
  have hex : ∀ α : Finset (Fin j), ∃ β : Finset (Fin k), α.card = 4 →
      β.card = 4 ∧ ((kleinOn α).subgroupOf (alternatingGroup (Fin j))).map ρ = kleinOn β := by
    intro α
    by_cases hα : α.card = 4
    · obtain ⟨M, hM, hlab⟩ := I.label_surj α hα true
      obtain ⟨β, hβ, d, hlab'⟩ := I'.label M (hPP hM)
      exact ⟨β, fun _ => ⟨hβ, hKey M hM α hα true β hβ d hlab hlab'⟩⟩
    · exact ⟨∅, fun h => absurd h hα⟩
  choose f hf using hex
  obtain ⟨ι, hι⟩ := exists_emb_core hj5 ρ hρinj f (fun α hα => (hf α hα).1)
    (fun α hα => (hf α hα).2)
  refine ⟨ι, fun L hL α hα b hLα => ?_⟩
  obtain ⟨β, hβ, d, hlab'⟩ := I'.label L (hPP hL)
  have hβf : β = f α :=
    eq_of_kleinOn_eq hβ (hf α hα).1 ((hKey L hL α hα b β hβ d hLα hlab').symm.trans (hf α hα).2)
  rw [hι α hα] at hβf
  subst hβf
  exact ⟨hβ, d, hlab'⟩

theorem exists_emb_of_aeIdent_small_eq [Finite G] {P P' : Set (Subgroup G)} (hPP : P ⊆ P')
    {j : ℕ} (hj5 : 5 ≤ j) (I : AEIdent P j) (I' : AEIdent P' (j + 2))
    (hH : TL4.AECoverHyp I) (hzL : ∀ L ∈ P, ∃ u, IsUniqueInvolution L u) :
    ∃ ι : Fin j ↪ Fin (j + 2), ∀ L ∈ P, ∀ (α : Finset (Fin j)) (hα : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan P)).map I.φ = memBar α hα b →
      ∃ (hα' : (α.map ι).card = 4) (b' : Bool),
        (L.subgroupOf (pSpan P')).map I'.φ = memBar (α.map ι) hα' b' :=
  exists_emb_of_aeIdent_small' hPP hj5 (by omega) I I' hH hzL

end CFSG.ClassicalInvolution.Q3.TC.Thin
