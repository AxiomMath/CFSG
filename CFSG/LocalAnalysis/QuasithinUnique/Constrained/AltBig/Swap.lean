module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Basic
public import CFSG.Quasithin.Background.B1More13A

public section

namespace CFSG.QuasithinUnique.L246C127.AltBig

open Equiv Equiv.Perm Subgroup CFSG.Open
open scoped commutatorElement

section TC

variable {β : Type} [Fintype β] [DecidableEq β]

def swapClos (R : Subgroup (Perm β)) : Subgroup (Perm β) :=
  Subgroup.closure {σ | σ ∈ R ∧ σ.IsSwap}

open scoped Classical in
noncomputable def cls (R : Subgroup (Perm β)) (x : β) : Finset β :=
  Finset.univ.filter fun y => y = x ∨ swap x y ∈ R

def altOn (C : Finset β) : Subgroup (Perm β) :=
  alternatingGroup β ⊓ fixOn ((C : Set β)ᶜ)

theorem mem_cls {R : Subgroup (Perm β)} {x y : β} : y ∈ cls R x ↔ y = x ∨ swap x y ∈ R := by
  classical
  simp [cls]

theorem swapClos_le (R : Subgroup (Perm β)) : swapClos R ≤ R := by
  unfold swapClos
  rw [Subgroup.closure_le]
  intro σ hσ
  exact hσ.1

theorem swapClos_normal (R : Subgroup (Perm β)) : ((swapClos R).subgroupOf R).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (swapClos_le R)]
  intro h k hh hk
  have key : swapClos R ≤ (swapClos R).comap (MulAut.conj k).toMonoidHom := by
    unfold swapClos
    rw [Subgroup.closure_le]
    rintro σ ⟨hσR, x, y, hxy, rfl⟩
    show k * swap x y * k⁻¹ ∈ swapClos R
    rw [← Equiv.swap_apply_apply]
    have hmem : swap (k x) (k y) ∈ R := by
      rw [Equiv.swap_apply_apply]
      exact R.mul_mem (R.mul_mem hk hσR) (R.inv_mem hk)
    apply Subgroup.subset_closure
    exact ⟨hmem, k x, k y, k.injective.ne hxy, rfl⟩
  exact key hh

theorem cls_self (R : Subgroup (Perm β)) (x : β) : x ∈ cls R x := by
  rw [mem_cls]
  exact Or.inl rfl

theorem cls_symm {R : Subgroup (Perm β)} {x y : β} (h : y ∈ cls R x) : x ∈ cls R y := by
  rw [mem_cls] at h ⊢
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [swap_comm]; exact h)

theorem cls_trans {R : Subgroup (Perm β)} {x y z : β} (h : y ∈ cls R x) (h' : z ∈ cls R y) :
    z ∈ cls R x := by
  rw [mem_cls] at h h' ⊢
  by_cases hz : z = x
  · exact Or.inl hz
  right
  rcases h with hy | hxy
  · rw [hy] at h'
    rcases h' with h1 | h1
    · exact absurd h1 hz
    · exact h1
  · rcases h' with hzy | hyz
    · rw [hzy]
      exact hxy
    · by_cases hxy' : x = y
      · rw [← hxy'] at hyz
        exact hyz
      · have e : swap y z * swap x y * swap y z = swap z x :=
          Equiv.swap_mul_swap_mul_swap hxy' (Ne.symm hz)
        rw [swap_comm, ← e]
        exact R.mul_mem (R.mul_mem hyz hxy) hyz

theorem swap_mem_of_mem_cls {R : Subgroup (Perm β)} {x a b : β} (ha : a ∈ cls R x)
    (hb : b ∈ cls R x) : swap a b ∈ R := by
  by_cases hab : a = b
  · rw [hab, swap_self, ← Equiv.Perm.one_def]
    exact R.one_mem
  · have hba : b ∈ cls R a := cls_trans (cls_symm ha) hb
    rw [mem_cls] at hba
    rcases hba with h1 | h1
    · exact absurd h1.symm hab
    · exact h1

theorem swapClos_mem_cls {R : Subgroup (Perm β)} {g : Perm β} (hg : g ∈ swapClos R) {x y : β}
    (hy : y ∈ cls R x) : g y ∈ cls R x := by
  have key : ∀ σ ∈ swapClos R, ∀ z : β, z ∈ cls R x ↔ σ z ∈ cls R x := by
    intro σ hσ
    unfold swapClos at hσ
    induction hσ using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨hsR, a, b, -, rfl⟩ := hs
      have h1 : b ∈ cls R a := mem_cls.mpr (Or.inr hsR)
      have h2 : a ∈ cls R b := mem_cls.mpr (Or.inr (by rw [swap_comm]; exact hsR))
      have hiff : a ∈ cls R x ↔ b ∈ cls R x :=
        ⟨fun ha => cls_trans ha h1, fun hb => cls_trans hb h2⟩
      intro z
      by_cases hza : z = a
      · rw [hza, swap_apply_left]
        exact hiff
      · by_cases hzb : z = b
        · rw [hzb, swap_apply_right]
          exact hiff.symm
        · rw [swap_apply_of_ne_of_ne hza hzb]
    | one =>
      intro z
      exact Iff.rfl
    | mul s t hs ht ihs iht =>
      intro z
      rw [Equiv.Perm.mul_apply]
      exact (iht z).trans (ihs (t z))
    | inv s hs ihs =>
      intro z
      have e : s (s⁻¹ z) = z := by
        rw [Equiv.Perm.inv_def]
        exact Equiv.apply_symm_apply s z
      have h := ihs (s⁻¹ z)
      rw [e] at h
      exact h.symm
  exact (key g hg y).mp hy

theorem mem_altOn {C : Finset β} {σ : Perm β} :
    σ ∈ altOn C ↔ σ ∈ alternatingGroup β ∧ ∀ z, z ∉ C → σ z = z := by
  simp only [altOn, Subgroup.mem_inf, mem_fixOn, Set.mem_compl_iff, Finset.mem_coe]

theorem altOn_eq_map (C : Finset β) :
    altOn C = (alternatingGroup ↥C).map (Equiv.Perm.ofSubtype : Perm ↥C →* Perm β) := by
  ext σ
  rw [mem_altOn, Subgroup.mem_map]
  constructor
  · rintro ⟨hσ, hfix⟩
    have hiff : ∀ x, σ x ∈ C ↔ x ∈ C := by
      intro x
      constructor
      · intro hsx
        by_contra hx
        rw [hfix x hx] at hsx
        exact hx hsx
      · intro hx
        by_contra hsx
        have h1 : σ x = x := σ.injective (hfix (σ x) hsx)
        exact hsx (by rw [h1]; exact hx)
    have h2 : ∀ x, σ x ≠ x → x ∈ C := by
      intro x hx
      by_contra hC
      exact hx (hfix x hC)
    refine ⟨σ.subtypePerm (p := fun y => y ∈ C) hiff, ?_,
      Equiv.Perm.ofSubtype_subtypePerm (p := fun y => y ∈ C) hiff h2⟩
    have hs := Equiv.Perm.sign_subtypePerm (p := fun y => y ∈ C) σ hiff h2
    rw [Equiv.Perm.mem_alternatingGroup]
    convert hs.trans (Equiv.Perm.mem_alternatingGroup.mp hσ)
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨?_, fun z hz => Equiv.Perm.ofSubtype_apply_of_not_mem τ hz⟩
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_ofSubtype]
    exact Equiv.Perm.mem_alternatingGroup.mp hτ

theorem altOn_equiv (C : Finset β) : Nonempty (↥(altOn C) ≃* alternatingGroup ↥C) := by
  have hinj : Function.Injective (Equiv.Perm.ofSubtype : Perm ↥C →* Perm β) :=
    Equiv.Perm.ofSubtype_injective
  exact ⟨(MulEquiv.subgroupCongr (altOn_eq_map C)).trans
    (Subgroup.equivMapOfInjective (alternatingGroup ↥C)
      (Equiv.Perm.ofSubtype : Perm ↥C →* Perm β) hinj).symm⟩

theorem altOn_simple {C : Finset β} (h : 5 ≤ C.card) : IsSimpleGroup ↥(altOn C) := by
  obtain ⟨e⟩ := altOn_equiv C
  have hcard : 5 ≤ Nat.card ↥C := by
    rw [Nat.card_eq_finsetCard]
    exact h
  haveI := alternatingGroup.isSimpleGroup hcard
  exact e.isSimpleGroup

theorem altOn_solvable {C : Finset β} (h : C.card ≤ 4) : Group.IsSolvable ↥(altOn C) := by
  obtain ⟨e⟩ := altOn_equiv C
  have hcard : Nat.card ↥C ≤ 4 := by
    rw [Nat.card_eq_finsetCard]
    exact h
  haveI := alternatingGroup.isSolvable hcard
  exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem altOn_le_swapClos (R : Subgroup (Perm β)) (x : β) : altOn (cls R x) ≤ swapClos R := by
  have hclos : Subgroup.closure {σ : Perm ↥(cls R x) | σ.IsSwap} ≤
      (swapClos R).comap (Equiv.Perm.ofSubtype : Perm ↥(cls R x) →* Perm β) := by
    rw [Subgroup.closure_le]
    rintro τ ⟨a, b, hab, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Equiv.Perm.ofSubtype_swap_eq]
    unfold swapClos
    exact Subgroup.subset_closure
      ⟨swap_mem_of_mem_cls a.2 b.2, (a : β), (b : β), fun h => hab (Subtype.ext h), rfl⟩
  rw [Equiv.Perm.closure_isSwap] at hclos
  rw [altOn_eq_map, Subgroup.map_le_iff_le_comap]
  intro τ _
  exact hclos (Subgroup.mem_top τ)

theorem ftc7_comm_apply {σ c : Perm β} (h : σ * c = c * σ) (x : β) :
    σ (c x) = c (σ x) := by
  have := congrArg (fun π : Perm β => π x) h
  simpa only [Perm.mul_apply] using this

theorem ftc7_mem_of_comm {a b d : β} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) {σ : Perm β}
    (hσ : σ * (swap a b * swap a d) = (swap a b * swap a d) * σ) :
    σ a = a ∨ σ a = b ∨ σ a = d := by
  by_contra hne
  rw [not_or, not_or] at hne
  obtain ⟨h1, h2, h3⟩ := hne
  have hca : (swap a b * swap a d) a = d := by
    simp [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, had.symm, hbd.symm]
  have hfix : (swap a b * swap a d) (σ a) = σ a := by
    simp [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, h1, h2, h3]
  have h4 := ftc7_comm_apply hσ a
  rw [hca, hfix] at h4
  exact had (σ.injective h4).symm

theorem ftc7_three_cases {a b d : β} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) {σ : Perm β}
    (hσ : σ * (swap a b * swap a d) = (swap a b * swap a d) * σ) :
    (σ a = a ∧ σ b = b ∧ σ d = d) ∨ (σ a = d ∧ σ b = a ∧ σ d = b) ∨
      (σ a = b ∧ σ b = d ∧ σ d = a) := by
  have hca : (swap a b * swap a d) a = d := by
    simp [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, had.symm, hbd.symm]
  have hcb : (swap a b * swap a d) b = a := by
    simp [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, hab.symm, hbd]
  have hcd : (swap a b * swap a d) d = b := by
    simp [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, had, hbd]
  have e1 : σ d = (swap a b * swap a d) (σ a) := by
    have h := ftc7_comm_apply hσ a
    rwa [hca] at h
  have e2 : σ b = (swap a b * swap a d) (σ d) := by
    have h := ftc7_comm_apply hσ d
    rwa [hcd] at h
  rcases ftc7_mem_of_comm hab had hbd hσ with h | h | h
  · have hd : σ d = d := by rw [e1, h, hca]
    have hb : σ b = b := by rw [e2, hd, hcd]
    exact Or.inl ⟨h, hb, hd⟩
  · have hd : σ d = a := by rw [e1, h, hcb]
    have hb : σ b = d := by rw [e2, hd, hca]
    exact Or.inr (Or.inr ⟨h, hb, hd⟩)
  · have hd : σ d = b := by rw [e1, h, hcd]
    have hb : σ b = a := by rw [e2, hd, hcb]
    exact Or.inr (Or.inl ⟨h, hb, hd⟩)

theorem ftc7_comm_swap3 {R : Subgroup (Perm β)} {E : Subgroup (Perm β)}
    (h : ∀ x, 3 ≤ (cls R x).card → ⁅E, altOn (cls R x)⁆ = ⊥) {x a b d : β}
    (ha : a ∈ cls R x) (hb : b ∈ cls R x) (hd : d ∈ cls R x) (hab : a ≠ b) (had : a ≠ d)
    (hbd : b ≠ d) (hcard : 3 ≤ (cls R x).card) {e : Perm β} (he : e ∈ E) :
    e * (swap a b * swap a d) = (swap a b * swap a d) * e := by
  have hc : swap a b * swap a d ∈ altOn (cls R x) := by
    rw [mem_altOn]
    refine ⟨?_, fun z hz => ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
        Equiv.Perm.sign_swap had]
      all_goals first | exact Int.units_mul_self _ | decide | norm_num
    · have hza : z ≠ a := by
        rintro rfl
        exact hz ha
      have hzb : z ≠ b := by
        rintro rfl
        exact hz hb
      have hzd : z ≠ d := by
        rintro rfl
        exact hz hd
      simp [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, hza, hzb, hzd]
  have hmem : ⁅e, swap a b * swap a d⁆ ∈ ⁅E, altOn (cls R x)⁆ :=
    Subgroup.commutator_mem_commutator he hc
  rw [h x hcard, Subgroup.mem_bot] at hmem
  exact commutatorElement_eq_one_iff_mul_comm.mp hmem

theorem ftc7_eq_of_three {s y b d g : β} (hby : b ≠ y) (hdy : d ≠ y) (hgy : g ≠ y)
    (hbd : b ≠ d) (hbg : b ≠ g) (hdg : d ≠ g)
    (k1 : s = y ∨ s = b ∨ s = d) (k2 : s = y ∨ s = b ∨ s = g) (k3 : s = y ∨ s = d ∨ s = g) :
    s = y := by
  by_contra hne
  rcases k1 with h1 | h1 | h1 <;> rcases k2 with h2 | h2 | h2 <;>
    rcases k3 with h3 | h3 | h3 <;> simp_all

theorem ftc7_fix_of_card_ge_four {R : Subgroup (Perm β)} {E : Subgroup (Perm β)}
    (h : ∀ x, 3 ≤ (cls R x).card → ⁅E, altOn (cls R x)⁆ = ⊥) {x y : β} (hy : y ∈ cls R x)
    (hcard : 4 ≤ (cls R x).card) {e : Perm β} (he : e ∈ E) : e y = y := by
  have h2 : 2 < ((cls R x).erase y).card := by
    rw [Finset.card_erase_of_mem hy]
    omega
  obtain ⟨b, hb, d, hd, g, hg, hbd, hbg, hdg⟩ := Finset.two_lt_card.mp h2
  obtain ⟨hby, hb⟩ := Finset.mem_erase.mp hb
  obtain ⟨hdy, hd⟩ := Finset.mem_erase.mp hd
  obtain ⟨hgy, hg⟩ := Finset.mem_erase.mp hg
  have hy1 : y ≠ b := Ne.symm hby
  have hy2 : y ≠ d := Ne.symm hdy
  have hy3 : y ≠ g := Ne.symm hgy
  have k1 := ftc7_mem_of_comm hy1 hy2 hbd
    (ftc7_comm_swap3 h hy hb hd hy1 hy2 hbd (by omega) he)
  have k2 := ftc7_mem_of_comm hy1 hy3 hbg
    (ftc7_comm_swap3 h hy hb hg hy1 hy3 hbg (by omega) he)
  have k3 := ftc7_mem_of_comm hy2 hy3 hdg
    (ftc7_comm_swap3 h hy hd hg hy2 hy3 hdg (by omega) he)
  exact ftc7_eq_of_three hby hdy hgy hbd hbg hdg k1 k2 k3

theorem ftc7_perm_pair {p q : β} (hpq : p ≠ q) {σ : Perm β} (hp : σ p = p ∨ σ p = q)
    (hq : σ q = p ∨ σ q = q) : (σ p = p ∧ σ q = q) ∨ (σ p = q ∧ σ q = p) := by
  rcases hp with h1 | h1 <;> rcases hq with h2 | h2
  · exact absurd (σ.injective (h1.trans h2.symm)) hpq
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (σ.injective (h1.trans h2.symm)) hpq

theorem ftc7_comm_on_pair {p q : β} {σ τ : Perm β}
    (hσ : (σ p = p ∧ σ q = q) ∨ (σ p = q ∧ σ q = p))
    (hτ : (τ p = p ∧ τ q = q) ∨ (τ p = q ∧ τ q = p)) :
    σ (τ p) = τ (σ p) ∧ σ (τ q) = τ (σ q) := by
  rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hτ with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    simp [h1, h2, h3, h4]

theorem ftc7_comm_of_card_three {R : Subgroup (Perm β)} {E : Subgroup (Perm β)}
    (h : ∀ x, 3 ≤ (cls R x).card → ⁅E, altOn (cls R x)⁆ = ⊥) {x y : β} (hy : y ∈ cls R x)
    (hcard : (cls R x).card = 3) {e f : Perm β} (he : e ∈ E) (hf : f ∈ E) :
    e (f y) = f (e y) := by
  obtain ⟨a, b, d, hab, had, hbd, hC⟩ := Finset.card_eq_three.mp hcard
  have ha : a ∈ cls R x := by
    rw [hC]
    simp
  have hb : b ∈ cls R x := by
    rw [hC]
    simp
  have hd : d ∈ cls R x := by
    rw [hC]
    simp
  have hy3 : y = a ∨ y = b ∨ y = d := by
    rw [hC] at hy
    simpa using hy
  have hce := ftc7_comm_swap3 h ha hb hd hab had hbd (by omega) he
  have hcf := ftc7_comm_swap3 h ha hb hd hab had hbd (by omega) hf
  rcases ftc7_three_cases hab had hbd hce with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
  rcases ftc7_three_cases hab had hbd hcf with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ <;>
  rcases hy3 with hy3 | hy3 | hy3 <;>
  simp only [hy3, h1, h2, h3, k1, k2, k3]

theorem ftc7_comm_of_card_le_two {R : Subgroup (Perm β)} {E : Subgroup (Perm β)}
    (hE : E ≤ swapClos R) {x y : β} (hy : y ∈ cls R x) (hcard : (cls R x).card ≤ 2)
    {e f : Perm β} (he : e ∈ E) (hf : f ∈ E) : e (f y) = f (e y) := by
  have hsub : ∀ σ ∈ E, ∀ u ∈ cls R x, σ u ∈ cls R x :=
    fun σ hσ u hu => swapClos_mem_cls (hE hσ) hu
  rcases Nat.lt_or_ge (cls R x).card 2 with h1 | h2
  · have hone : ∀ u ∈ cls R x, u = y := fun u hu => Finset.card_le_one.mp (by omega) u hu y hy
    have hey : e y = y := hone _ (hsub e he y hy)
    have hfy : f y = y := hone _ (hsub f hf y hy)
    simp [hey, hfy]
  · obtain ⟨p, q, hpq, hC⟩ := Finset.card_eq_two.mp (by omega : (cls R x).card = 2)
    have hmem : ∀ u ∈ cls R x, u = p ∨ u = q := by
      intro u hu
      rw [hC] at hu
      simpa using hu
    have hp : p ∈ cls R x := by
      rw [hC]
      simp
    have hq : q ∈ cls R x := by
      rw [hC]
      simp
    have hσe := ftc7_perm_pair hpq (hmem _ (hsub e he p hp)) (hmem _ (hsub e he q hq))
    have hσf := ftc7_perm_pair hpq (hmem _ (hsub f hf p hp)) (hmem _ (hsub f hf q hq))
    have key := ftc7_comm_on_pair hσe hσf
    rcases hmem y hy with h | h
    · rw [h]
      exact key.1
    · rw [h]
      exact key.2

theorem altOn_normal (R : Subgroup (Perm β)) (x : β) :
    ((altOn (cls R x)).subgroupOf (swapClos R)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  rw [mem_altOn] at hn ⊢
  refine ⟨?_, fun z hz => ?_⟩
  · have hc := (inferInstance : (alternatingGroup β).Normal).conj_mem _ hn.1 (g : Perm β)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hc
  · have hw : (g : Perm β)⁻¹ z ∉ cls R x := by
      intro hw'
      apply hz
      simpa using swapClos_mem_cls g.2 hw'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply]
    rw [hn.2 _ hw]
    simp

theorem comm_of_comm_alts (R : Subgroup (Perm β)) {E : Subgroup (Perm β)} (hE : E ≤ swapClos R)
    (h : ∀ x, 3 ≤ (cls R x).card → ⁅E, altOn (cls R x)⁆ = ⊥) :
    ∀ e ∈ E, ∀ f ∈ E, Commute e f := by
  intro e he f hf
  show e * f = f * e
  ext y
  simp only [Perm.mul_apply]
  have hy : y ∈ cls R y := cls_self R y
  rcases Nat.lt_or_ge (cls R y).card 4 with h4 | h4
  · rcases Nat.lt_or_ge (cls R y).card 3 with h3 | h3
    · exact ftc7_comm_of_card_le_two hE hy (by omega) he hf
    · exact ftc7_comm_of_card_three h hy (by omega) he hf
  · have hey := ftc7_fix_of_card_ge_four h hy h4 he
    have hfy := ftc7_fix_of_card_ge_four h hy h4 hf
    simp [hey, hfy]

theorem tcPerfectOfQuasisimple {G : Type} [Group G] {E : Subgroup G}
    (h : CFSG.Open.IsQuasisimple ↥E) : ⁅E, E⁆ = E := by
  obtain ⟨hc, -⟩ := h
  have h1 : (⊤ : Subgroup ↥E).map E.subtype = E := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h2 : (_root_.commutator ↥E).map E.subtype = ⁅E, E⁆ := by
    unfold _root_.commutator
    rw [Subgroup.map_commutator, h1]
  rw [← h2, hc, h1]

theorem tcNeBotOfQuasisimple {G : Type} [Group G] {E : Subgroup G}
    (h : CFSG.Open.IsQuasisimple ↥E) : E ≠ ⊥ := by
  obtain ⟨-, hs⟩ := h
  intro hE
  have hone : ∀ x : ↥E, x = 1 := by
    intro x
    rw [Subgroup.eq_bot_iff_forall] at hE
    exact Subtype.ext (hE x x.2)
  obtain ⟨a, b, hab⟩ := exists_pair_ne (↥E ⧸ Subgroup.center ↥E)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [hone a, hone b])

theorem tc (q : FpfInv β) {R : Subgroup (Perm β)} (hq : ∀ x, swap x (q.μ x) ∈ R)
    {E : Subgroup (Perm β)} (hE : IsComponentOf E R) :
    ∃ C : Finset β, 5 ≤ C.card ∧ (∀ x ∈ C, q.μ x ∈ C) ∧ E = altOn C := by
  have hperf : ⁅E, E⁆ = E := tcPerfectOfQuasisimple hE.2.2
  have hne : E ≠ ⊥ := tcNeBotOfQuasisimple hE.2.2
  have hcT : _root_.commutator ↥E = ⊤ := by
    obtain ⟨hc, -⟩ := hE.2.2
    exact hc
  have hsub : CFSG.Open.IsSubnormal (swapClos R) R :=
    CFSG.Open.IsSubnormal.step (swapClos_le R) (swapClos_normal R)
      (CFSG.Open.IsSubnormal.refl R)
  have hswapmem : ∀ x, swap x (q.μ x) ∈ swapClos R := by
    intro x
    have hsw : (swap x (q.μ x)).IsSwap := ⟨x, q.μ x, Ne.symm (q.fpf x), rfl⟩
    exact Subgroup.subset_closure ⟨hq x, hsw⟩
  rcases CFSG.Quasithin.B113.component_le_or_commutator_eq_bot hE hsub with hEswap | hcomm
  ·
    have hEsub : CFSG.Open.IsSubnormal E (swapClos R) := by
      have h := CFSG.Quasithin.B113.isSubnormal_inf_of_le hE.2.1 (swapClos_le R)
      rwa [inf_of_le_right hEswap] at h
    have hEcomp : IsComponentOf E (swapClos R) := ⟨hEswap, hEsub, hE.2.2⟩
    obtain ⟨x0, -, hx0E⟩ : ∃ x, 3 ≤ (cls R x).card ∧ E ≤ altOn (cls R x) := by
      by_contra H
      have hcomm_all : ∀ x, 3 ≤ (cls R x).card → ⁅E, altOn (cls R x)⁆ = ⊥ := by
        intro x hx
        have hX : CFSG.Open.IsSubnormal (altOn (cls R x)) (swapClos R) :=
          CFSG.Open.IsSubnormal.step (altOn_le_swapClos R x) (altOn_normal R x)
            (CFSG.Open.IsSubnormal.refl (swapClos R))
        rcases CFSG.Quasithin.B113.component_le_or_commutator_eq_bot hEcomp hX with h | h
        · exact absurd ⟨x, hx, h⟩ H
        · exact h
      have hEE : ⁅E, E⁆ = ⊥ := by
        rw [← le_bot_iff, Subgroup.commutator_le]
        intro e he f hf
        rw [Subgroup.mem_bot]
        exact commutatorElement_eq_one_iff_mul_comm.2
          (comm_of_comm_alts R hEswap hcomm_all e he f hf).eq
      exact hne (hperf.symm.trans hEE)
    have hECsub : CFSG.Open.IsSubnormal E (altOn (cls R x0)) := by
      have h := CFSG.Quasithin.B113.isSubnormal_inf_of_le hEsub (altOn_le_swapClos R x0)
      rwa [inf_of_le_right hx0E] at h
    have hcard5 : 5 ≤ (cls R x0).card := by
      by_contra hlt
      have hsolv : Group.IsSolvable ↥(altOn (cls R x0)) := altOn_solvable (by omega)
      have hsolvE : Group.IsSolvable ↥E :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hx0E)
      haveI : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot E).2 hne
      have hlt' := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥E
      rw [hcT] at hlt'
      exact lt_irrefl _ hlt'
    have hsimple : IsSimpleGroup ↥(altOn (cls R x0)) := altOn_simple hcard5
    refine ⟨cls R x0, hcard5, fun y hy => ?_, ?_⟩
    · have hmemy : q.μ y ∈ cls R y := mem_cls.2 (Or.inr (hq y))
      exact cls_trans hy hmemy
    · rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hECsub hsimple with h | h
      · exact absurd h hne
      · exact h
  ·
    exfalso
    apply hne
    have hfix : ∀ e ∈ E, ∀ x ∈ (Set.univ : Set β), e x = x ∨ e x = q.μ x := by
      intro e he x _
      have hmem : ⁅e, swap x (q.μ x)⁆ ∈ ⁅E, swapClos R⁆ :=
        Subgroup.commutator_mem_commutator he (hswapmem x)
      rw [hcomm, Subgroup.mem_bot] at hmem
      have hcm := commutatorElement_eq_one_iff_mul_comm.1 hmem
      have h1 : e (q.μ x) = swap x (q.μ x) (e x) := by
        have h' := congrArg (fun σ : Perm β => σ x) hcm
        simpa [Equiv.Perm.mul_apply, Equiv.swap_apply_left] using h'
      by_cases h2 : e x = x
      · exact Or.inl h2
      by_cases h3 : e x = q.μ x
      · exact Or.inr h3
      have h4 : swap x (q.μ x) (e x) = e x := Equiv.swap_apply_of_ne_of_ne h2 h3
      rw [h4] at h1
      exact absurd (e.injective h1) (q.fpf x)
    have hall := perfect_fix_pairs q hperf (W := Set.univ) hfix (fun x _ => Set.mem_univ _)
    rw [Subgroup.eq_bot_iff_forall]
    intro e he
    ext x
    simpa using hall e he x (Set.mem_univ x)

end TC

end CFSG.QuasithinUnique.L246C127.AltBig
