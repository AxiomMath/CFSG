module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Basic
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.QuasithinUnique.B42A57

open CFSG.Quasithin Equiv Equiv.Perm

variable {S : Type} [CommGroup S] [Finite S] {G L : Subgroup (MulAut S)} {m : ℕ}

theorem exists_embedding (C : Bridge.Alt57.Ctx G L m) :
    ∃ (ι : ↥L ≃* alternatingGroup (Fin m)) (e : ↥G →* Perm (Fin m)), Function.Injective e ∧
      (∀ l : ↥L, e ⟨(l : MulAut S), C.le_G l.2⟩ = (ι l : Perm (Fin m))) ∧
      ∀ (g : ↥G) (l l' : ↥L), (g : MulAut S) * (l : MulAut S) * (g : MulAut S)⁻¹ = (l' : MulAut S) →
        (ι l' : Perm (Fin m)) = e g * (ι l : Perm (Fin m)) * (e g)⁻¹ := by
  obtain ⟨ι⟩ := C.iso
  have hm : 5 ≤ m ∧ m ≠ 6 := by rcases C.m_cases with h | h <;> omega
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m hm.1 hm.2
  let Ls : Subgroup ↥G := L.subgroupOf G
  have : Ls.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := C.normal g g.2 n hn
    simpa using this⟩
  let φ : ↥Ls ≃* alternatingGroup (Fin m) := (Subgroup.subgroupOfEquivOfLe C.le_G).trans ι
  let cEquiv : Perm (Fin m) ≃* MulAut (alternatingGroup (Fin m)) := MulEquiv.ofBijective _ hbij
  let ec : ↥G →* MulAut (alternatingGroup (Fin m)) :=
    (MulAut.congr φ).toMonoidHom.comp (MulAut.conjNormal (H := Ls))
  let e : ↥G →* Perm (Fin m) := cEquiv.symm.toMonoidHom.comp ec
  have hce : ∀ g : ↥G, MulAut.conjNormal (e g) = ec g := fun g => by
    show cEquiv (cEquiv.symm (ec g)) = ec g
    exact cEquiv.apply_symm_apply _
  let lsOf : ↥L → ↥Ls := fun l => ⟨⟨(l : MulAut S), C.le_G l.2⟩, Subgroup.mem_subgroupOf.2 l.2⟩
  have hφl : ∀ l : ↥L, φ (lsOf l) = ι l := fun l => rfl
  have hconj : ∀ (g : ↥G) (x : ↥Ls),
      (φ (MulAut.conjNormal g x) : Perm (Fin m)) = e g * (φ x : Perm (Fin m)) * (e g)⁻¹ := by
    intro g x
    have h1 := congrArg (fun f : MulAut (alternatingGroup (Fin m)) =>
      ((f (φ x) : alternatingGroup (Fin m)) : Perm (Fin m))) (hce g)
    simp only [MulAut.conjNormal_apply] at h1
    rw [h1]
    simp [ec, MulAut.congr_apply]
  have hconjL : ∀ (g : ↥G) (l l' : ↥L),
      (g : MulAut S) * (l : MulAut S) * (g : MulAut S)⁻¹ = (l' : MulAut S) →
        (ι l' : Perm (Fin m)) = e g * (ι l : Perm (Fin m)) * (e g)⁻¹ := by
    intro g l l' hll'
    have h := hconj g (lsOf l)
    have e1 : MulAut.conjNormal g (lsOf l) = lsOf l' := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using hll'
    rw [e1, hφl, hφl] at h
    exact h
  have hinj : Function.Injective e := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hcent : ∀ l ∈ L, (g : MulAut S) * l = l * (g : MulAut S) := by
      intro l hl
      have hl'' : (g : MulAut S) * l * (g : MulAut S)⁻¹ ∈ L := C.normal g g.2 l hl
      have h := hconjL g ⟨l, hl⟩ ⟨_, hl''⟩ rfl
      rw [hg] at h
      simp only [one_mul, inv_one, mul_one] at h
      have h2 : (⟨(g : MulAut S) * l * (g : MulAut S)⁻¹, hl''⟩ : ↥L) = ⟨l, hl⟩ :=
        ι.injective (Subtype.ext h)
      have h3 := congrArg Subtype.val h2
      simp only at h3
      calc (g : MulAut S) * l = (g : MulAut S) * l * (g : MulAut S)⁻¹ * (g : MulAut S) := by group
        _ = l * (g : MulAut S) := by rw [h3]
    exact Subtype.ext (C.cent_trivial g g.2 hcent)
  have hL : ∀ l : ↥L, e ⟨(l : MulAut S), C.le_G l.2⟩ = (ι l : Perm (Fin m)) := by
    intro l
    apply hbij.1
    rw [hce]
    ext a
    obtain ⟨y, rfl⟩ := φ.surjective a
    have h1 : (ec ⟨(l : MulAut S), C.le_G l.2⟩) (φ y) = φ (MulAut.conjNormal ⟨(l : MulAut S), C.le_G l.2⟩ y) := by
      simp [ec, MulAut.congr_apply]
    rw [h1]
    have e1 : MulAut.conjNormal (⟨(l : MulAut S), C.le_G l.2⟩ : ↥G) y =
        lsOf l * y * (lsOf l)⁻¹ := by
      apply Subtype.ext
      simp [lsOf]
    rw [e1, map_mul, map_mul, map_inv, hφl]
    simp
  exact ⟨ι, e, hinj, hL, hconjL⟩

end CFSG.QuasithinUnique.B42A57
