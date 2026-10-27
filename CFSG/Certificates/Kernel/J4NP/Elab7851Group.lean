module

public import CFSG.Certificates.Kernel.J4NP.Elab7851Facts
public import CFSG.Certificates.Kernel.J4NP.Elab7851Chain
public import CFSG.Sporadic.J4.QTRankProof
public import CFSG.Sporadic.J4

public section

namespace CFSG.KC.J4NP

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.KC.J4Loc Classical

theorem mem_Eg_of_acts
    {g g' : J} (hg : g ∈ P0) (hg' : g' ∈ P0) {t : List ℕ}
    (h : Acts g t) (h' : Acts g' t) : g⁻¹ * g' ∈ Eg uJ 11 := by
  have hF := j4Facts
  refine centralizer_Hj hF.mat hF _ (Hj.mul_mem (Hj.inv_mem (P0_le_Hj hg)) (P0_le_Hj hg'))
    fun y hy => ?_
  obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hF.mat)).1 hy
  have e1 := h.2 c hc
  have e2 := h'.2 c hc
  calc g⁻¹ * g' * eta uJ 11 c = g⁻¹ * (g' * eta uJ 11 c * g'⁻¹) * g' := by group
    _ = g⁻¹ * (g * eta uJ 11 c * g⁻¹) * g' := by rw [e1, e2]
    _ = eta uJ 11 c * (g⁻¹ * g') := by group

theorem tab_inv
    {x : J} (hx : x ∈ P0) (hxE : x ∉ Eg uJ 11) (hsq : x * x = 1)
    {t : List ℕ} (hxt : Acts x t) : t ≠ idT ∧ compT t t = idT := by
  have hF := j4Facts
  have hM := hF.mat
  refine ⟨fun h2 => ?_, ?_⟩
  · subst h2
    apply hxE
    refine centralizer_Hj hM hF x (P0_le_Hj hx) (fun y hy => ?_)
    obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hy
    have := hxt.2 c hc
    rw [actT_idT hc] at this
    calc x * eta uJ 11 c = (x * eta uJ 11 c * x⁻¹) * x := by group
      _ = eta uJ 11 c * x := by rw [this]
  · have h := hxt.mul hxt
    rw [hsq] at h
    exact h.unique hM Acts.one

noncomputable def posJ (KK : ℕ) (g : J) : ℕ :=
  if h : ∃ i, i < 191 ∧ Acts g (ivt KK i) then Nat.find h else 0

theorem posJ_spec
    {KK CMK PRK FMK MK : ℕ} {ENT : List (List (List (List ℕ)))}
    (hf : Facts7851 KK CMK PRK FMK MK ENT) {g : J} (hg : g ∈ P0) (hgE : g ∉ Eg uJ 11)
    (hsq : g * g = 1) : posJ KK g < 191 ∧ Acts g (ivt KK (posJ KK g)) := by
  have hM := j4Facts.mat
  obtain ⟨t, htL, hgt⟩ := table_of_mem hM g hg
  obtain ⟨hne, hinv⟩ := tab_inv hg hgE hsq hgt
  obtain ⟨i, hi, hit⟩ := hf.inv t htL hne hinv
  have hex : ∃ i, i < 191 ∧ Acts g (ivt KK i) := ⟨i, hi, hit ▸ hgt⟩
  unfold posJ
  rw [dif_pos hex]
  exact Nat.find_spec hex

theorem posJ_of_acts
    {KK CMK PRK FMK MK : ℕ} {ENT : List (List (List (List ℕ)))}
    (hf : Facts7851 KK CMK PRK FMK MK ENT) {g : J} (hg : g ∈ P0) (hgE : g ∉ Eg uJ 11)
    (hsq : g * g = 1) {p : ℕ} (hp : p < 191) (hgp : Acts g (ivt KK p)) : posJ KK g = p := by
  have hM := j4Facts.mat
  obtain ⟨h1, h2⟩ := posJ_spec hf hg hgE hsq
  exact hf.inj _ h1 _ hp (h2.unique hM hgp)

theorem chainHyp
    {KK CMK PRK FMK MK : ℕ} {ENT : List (List (List (List ℕ)))}
    (hf : Facts7851 KK CMK PRK FMK MK ENT) {A : Subgroup J} (hA : A ≤ P0)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hsq : ∀ x ∈ A, x * x = 1) :
    ChainHyp A (Eg uJ 11) (posJ KK) 191 := by
  have hM := j4Facts.mat
  refine ⟨hcomm, hsq, fun g hg hgE => (posJ_spec hf (hA hg) hgE (hsq g hg)).1, ?_⟩
  intro g hg h hh hgE hhE
  obtain ⟨g1, g2⟩ := posJ_spec hf (hA hg) hgE (hsq g hg)
  obtain ⟨h1, h2⟩ := posJ_spec hf (hA hh) hhE (hsq h hh)
  constructor
  · intro he
    rw [he] at g2
    exact mem_Eg_of_acts (hA hg) (hA hh) g2 h2
  · intro hn
    have e : h = g * (g⁻¹ * h) := by group
    have hact : Acts h (ivt KK (posJ KK g)) := by
      rw [e]
      exact g2.mul_of_mem_Eg hM hn
    exact (posJ_of_acts hf (hA hh) hhE (hsq h hh) g1 hact).symm

theorem compT_comm {a b : J} {s t : List ℕ} (hab : a * b = b * a)
    (ha : Acts a s) (hb : Acts b t) : compT s t = compT t s := by
  have hM := j4Facts.mat
  have e1 := ha.mul hb
  have e2 := hb.mul ha
  rw [hab] at e1
  exact e1.unique hM e2

def IsEnt (MK : ℕ) (s : Finset ℕ) : Prop :=
  ∃ i < 7507, ∀ p, (lnS 191 MK i).testBit p = true ↔ p ∈ s

theorem complete
    {KK CMK PRK FMK MK : ℕ} {ENT : List (List (List (List ℕ)))}
    (hf : Facts7851 KK CMK PRK FMK MK ENT) {A : Subgroup J} (hA : A ≤ P0)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hsq : ∀ x ∈ A, x * x = 1) :
    IsEnt MK (posF (Eg uJ 11) (posJ KK) 191 (A : Set J)) := by
  have hc := chainHyp hf hA hcomm hsq
  refine chain hc (IsEnt MK) ⟨0, by norm_num, fun p => by rw [hf.root]; simp⟩ ?_ _
    ⟨fun x hx => hx, A.one_mem, fun a ha b hb => A.mul_mem ha hb⟩
  rintro H hH g hgA hgE hlt ⟨i, hi, hbits⟩
  obtain ⟨hx, hgx⟩ := posJ_spec hf (hA hgA) hgE (hsq g hgA)
  have hmemL : ∀ p, p ∈ entL ENT i ↔ p ∈ posF (Eg uJ 11) (posJ KK) 191 H := fun p => by
    rw [← (hf.ent i hi).1 p, hbits]
  have hpos : ∀ a ∈ entL ENT i, ∃ b ∈ H, b ∉ Eg uJ 11 ∧ posJ KK b = a := by
    intro a ha
    obtain ⟨-, b, hb, hbE, rfl⟩ := mem_posF.mp ((hmemL a).mp ha)
    exact ⟨b, hb, hbE, rfl⟩
  have hcm : ∀ b ∈ H, b ∉ Eg uJ 11 → posJ KK b < 191 ∧ posJ KK b ≠ posJ KK g ∧
      (lnS 191 CMK (posJ KK b)).testBit (posJ KK g) = true ∧
      (lnS 191 CMK (posJ KK g)).testBit (posJ KK b) = true := by
    intro b hb hbE
    have hbA := hH.1 hb
    obtain ⟨hb1, hbt⟩ := posJ_spec hf (hA hbA) hbE (hsq b hbA)
    have hne : posJ KK b ≠ posJ KK g := (hlt _ (mem_posF.mpr ⟨hb1, b, hb, hbE, rfl⟩)).ne
    have hct := compT_comm (hcomm b hbA g hgA) hbt hgx
    exact ⟨hb1, hne, hf.comm _ hb1 _ hx hne hct, hf.comm _ hx _ hb1 hne.symm hct.symm⟩
  have hlane : ∀ b ∈ H, b ∉ Eg uJ 11 → g * b ∉ Eg uJ 11 ∧
      fld 8 (lnS 1528 PRK (posJ KK g)) (posJ KK b) = posJ KK (g * b) := by
    intro b hb hbE
    have hbA := hH.1 hb
    obtain ⟨hb1, hbt⟩ := posJ_spec hf (hA hbA) hbE (hsq b hbA)
    obtain ⟨-, hne, -, hcx⟩ := hcm b hb hbE
    obtain ⟨hlt', hpr⟩ := hf.prod _ hx _ hb1 hne.symm hcx
    have hgbE : g * b ∉ Eg uJ 11 := by
      intro h
      apply hne
      refine (hc.pos_eq b hbA g hgA hbE hgE).mpr ?_
      have e : b⁻¹ * g = (g * b)⁻¹ * (g * g) := by group
      rw [e, hsq g hgA, mul_one]
      exact (Eg uJ 11).inv_mem h
    have hgbA := A.mul_mem hgA hbA
    have hact : Acts (g * b) (ivt KK (fld 8 (lnS 1528 PRK (posJ KK g)) (posJ KK b))) := by
      rw [hpr]
      exact hgx.mul hbt
    exact ⟨hgbE, (posJ_of_acts hf (hA hgbA) hgbE (hsq _ hgbA) hlt' hact).symm⟩
  obtain ⟨j, hj, hjb⟩ := hf.child i hi _ hx fun a ha => by
    obtain ⟨b, hb, hbE, rfl⟩ := hpos a ha
    exact ⟨hlt _ ((hmemL _).mp ha), (hcm b hb hbE).2.2.1⟩
  refine ⟨j, hj, fun p => ?_⟩
  rw [hjb, mem_posF]
  constructor
  · rintro (hp | rfl | ⟨a, ha, rfl⟩)
    · obtain ⟨hp1, b, hb, hbE, rfl⟩ := mem_posF.mp ((hmemL _).mp hp)
      exact ⟨hp1, b, Or.inl hb, hbE, rfl⟩
    · exact ⟨hx, g * 1, Or.inr ⟨1, hH.2.1, rfl⟩, by simpa using hgE, by simp⟩
    · obtain ⟨b, hb, hbE, rfl⟩ := hpos a ha
      obtain ⟨hgbE, hl⟩ := hlane b hb hbE
      have hgbA := A.mul_mem hgA (hH.1 hb)
      rw [hl]
      exact ⟨(posJ_spec hf (hA hgbA) hgbE (hsq _ hgbA)).1, g * b, Or.inr ⟨b, hb, rfl⟩, hgbE, rfl⟩
  · rintro ⟨hp1, b', hb', hbE', rfl⟩
    rcases hb' with hb' | ⟨b, hb, rfl⟩
    · exact Or.inl ((hmemL _).mpr (mem_posF.mpr ⟨hp1, b', hb', hbE', rfl⟩))
    · by_cases hbE : b ∈ Eg uJ 11
      · refine Or.inr (Or.inl ?_)
        refine ((hc.pos_eq g hgA (g * b) (A.mul_mem hgA (hH.1 hb)) hgE hbE').mpr ?_).symm
        simpa using hbE
      · refine Or.inr (Or.inr ⟨posJ KK b, (hmemL _).mpr (mem_posF.mpr
          ⟨(hcm b hb hbE).1, b, hb, hbE, rfl⟩), (hlane b hb hbE).2⟩)

theorem star_of_facts
    {KK CMK PRK FMK MK : ℕ} {ENT : List (List (List (List ℕ)))}
    (hf : Facts7851 KK CMK PRK FMK MK ENT) :
    ∀ A : Subgroup J, A ≤ P0 → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → (∀ x ∈ A, x * x = 1) →
      ¬ A ≤ Eg uJ 11 → Nat.card ↥A ≤ 2 ^ 10 := by
  intro A hA hcomm hsq hAE
  have hF := j4Facts
  have hM := hF.mat
  set S := posF (Eg uJ 11) (posJ KK) 191 (A : Set J) with hSdef
  obtain ⟨i, hi, hbits⟩ := complete hf hA hcomm hsq
  obtain ⟨hent, hnd⟩ := hf.ent i hi
  have hmemL : ∀ p, p ∈ entL ENT i ↔ p ∈ S := fun p => by rw [← hent p, hbits]
  have hSA : ∀ p ∈ S, p < 191 ∧ ∃ g ∈ A, g ∉ Eg uJ 11 ∧ Acts g (ivt KK p) := by
    intro p hp
    obtain ⟨hp1, b, hb, hbE, rfl⟩ := mem_posF.mp hp
    exact ⟨hp1, b, hb, hbE, (posJ_spec hf (hA hb) hbE (hsq b hb)).2⟩
  obtain ⟨x, hxA, hxE⟩ : ∃ x ∈ A, x ∉ Eg uJ 11 := by
    by_contra hcon
    push Not at hcon
    exact hAE hcon
  obtain ⟨hx1, -⟩ := posJ_spec hf (hA hxA) hxE (hsq x hxA)
  have hxS : posJ KK x ∈ S := mem_posF.mpr ⟨hx1, x, hxA, hxE, rfl⟩
  have hne : entL ENT i ≠ [] := by
    intro h
    have := (hmemL _).mpr hxS
    rw [h] at this
    exact List.not_mem_nil this
  have hlen : S.card = (entL ENT i).length := by
    rw [← List.toFinset_card_of_nodup hnd]
    congr 1
    ext p
    rw [List.mem_toFinset, hmemL]
  have hrel : (Eg uJ 11).relIndex A ≤ S.card + 1 := by
    have key : ∀ a : ↥A, ∃ t ∈ tabL, Acts (a : J) t := fun a => table_of_mem hM a (hA a.2)
    choose tab htabL htab using key
    set T : Finset (List ℕ) := insert idT (S.image fun i => ivt KK i) with hTdef
    have hT : ∀ a : ↥A, tab a ∈ T := by
      intro a
      by_cases ha : (a : J) ∈ Eg uJ 11
      · rw [(htab a).unique hM (Acts.of_mem_Eg hM ha)]
        exact Finset.mem_insert_self _ _
      · obtain ⟨h1, h2⟩ := posJ_spec hf (hA a.2) ha (hsq a a.2)
        refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨posJ KK a,
          mem_posF.mpr ⟨h1, a, a.2, ha, rfl⟩, ?_⟩)
        exact h2.unique hM (htab a)
    let ψ : ↥A ⧸ (Eg uJ 11).subgroupOf A → ↥T := fun q => ⟨tab q.out, hT q.out⟩
    have hψ : Function.Injective ψ := by
      intro q q' h
      have h' : tab q.out = tab q'.out := congrArg Subtype.val h
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have h'' := htab q'.out
      rw [← h'] at h''
      have := mem_Eg_of_acts (hA q.out.2) (hA q'.out.2) (htab q.out) h''
      simpa using this
    calc (Eg uJ 11).relIndex A = Nat.card (↥A ⧸ (Eg uJ 11).subgroupOf A) := by
          rw [Subgroup.relIndex, Subgroup.index_eq_card]
      _ ≤ Nat.card ↥T := Nat.card_le_card_of_injective ψ hψ
      _ = T.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      _ ≤ (S.image fun i => ivt KK i).card + 1 := Finset.card_insert_le _ _
      _ ≤ S.card + 1 := Nat.add_le_add_right Finset.card_image_le 1
  have hfixG : ∀ G F : List ℕ, (∀ g ∈ G, g ∈ S) →
      (∀ c < 2048, (∀ g ∈ G, actT (ivt KK g) c = c) → c ∈ F) →
      Nat.card ↥(Eg uJ 11 ⊓ A) ≤ F.length := by
    intro G F hG hGF
    have key : ∀ y : ↥(Eg uJ 11 ⊓ A), ∃ c, c < 2 ^ 11 ∧ (y : J) = eta uJ 11 c :=
      fun y => (mem_Eg_iff (elem_uJ hM)).1 (Subgroup.mem_inf.mp y.2).1
    choose f hf1 hf2 using key
    have hfL : ∀ y, f y ∈ F := by
      intro y
      refine hGF _ (by have := hf1 y; omega) fun g hg => ?_
      obtain ⟨-, a, haA, -, hat⟩ := hSA g (hG g hg)
      have h1 := hcomm a haA y (Subgroup.mem_inf.mp y.2).2
      have h2 := hat.2 (f y) (hf1 y)
      rw [← hf2 y] at h2
      have h3 : a * (y : J) * a⁻¹ = y := by rw [h1]; group
      rw [h3, hf2 y] at h2
      exact eta_inj hM _ (actT_lt hat.1 _) _ (hf1 y) h2.symm
    let φ : ↥(Eg uJ 11 ⊓ A) → {c : ℕ // c ∈ F} := fun y => ⟨f y, hfL y⟩
    have hφ : Function.Injective φ := by
      intro y z h
      have h' : f y = f z := congrArg Subtype.val h
      apply Subtype.ext
      rw [hf2 y, hf2 z, h']
    calc Nat.card ↥(Eg uJ 11 ⊓ A) ≤ Nat.card {c : ℕ // c ∈ F} :=
          Nat.card_le_card_of_injective φ hφ
      _ ≤ F.length := natCard_mem_le F
  have hmul := Subgroup.relIndex_mul_card (H := Eg uJ 11) (K := A)
  rcases hf.bound i hi hne with hsmall | ⟨G, F, hG, hGF, hbF⟩
  · obtain ⟨a, haL⟩ := List.exists_mem_of_ne_nil _ hne
    have haS := (hmemL a).mp haL
    obtain ⟨F, hF128, hFa⟩ := hf.fix128 a (hSA a haS).1
    have hE := hfixG [a] F (by simpa using haS) fun c hc h => hFa c hc (h a (by simp))
    have h8 : (entL ENT i).length + 1 ≤ 8 := by omega
    calc Nat.card ↥A = (Eg uJ 11).relIndex A * Nat.card ↥(Eg uJ 11 ⊓ A) := hmul.symm
      _ ≤ 8 * 128 := Nat.mul_le_mul (by omega) (hE.trans hF128)
      _ = 2 ^ 10 := by norm_num
  · have hE := hfixG G F (fun g hg => (hmemL g).mp (hG g hg).1)
      fun c hc h => hGF c hc fun g hg => (hf.fix g (hG g hg).2 c hc).mpr (h g hg)
    calc Nat.card ↥A = (Eg uJ 11).relIndex A * Nat.card ↥(Eg uJ 11 ⊓ A) := hmul.symm
      _ ≤ ((entL ENT i).length + 1) * F.length := Nat.mul_le_mul (by omega) hE
      _ = F.length * ((entL ENT i).length + 1) := mul_comm _ _
      _ ≤ 1024 := hbF
      _ = 2 ^ 10 := by norm_num

end CFSG.KC.J4NP

end
