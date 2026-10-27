module

public import CFSG.ClassicalInvolution.Asc77.AscT7C2RGen
public import CFSG.ClassicalInvolution.Asc77.AscS24BDefs
public import CFSG.ClassicalInvolution.Asc77.AscS24BFrame

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace S24B

open Equiv in
theorem perm4_cent_swap : ∀ x : Perm (Fin 4), ∀ a ∈ S4.swaps4, ∀ b ∈ S4.swaps4, a ≠ b →
    a * b = b * a → x * a = a * x → x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  decide +kernel

open Equiv in
theorem perm4_mul_swap_cube : ∀ a ∈ S4.swaps4, ∀ b ∈ S4.swaps4, a ≠ b → a * b = b * a →
    ∀ c ∈ S4.swaps4, c ≠ a → c ≠ b → (a * c) ^ 3 = 1 ∧ a * c ≠ 1 := by
  decide

open Equiv in
theorem perm4_inv_conj : ∀ x ∈ T7C2.invs4, ∀ a ∈ S4.swaps4, ∀ b ∈ S4.swaps4, a ≠ b →
    a * b = b * a →
      (∃ σ ∈ S4.perms4, σ * a * σ⁻¹ = x) ∨ (∃ σ ∈ S4.perms4, σ * (a * b) * σ⁻¹ = x) := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

namespace Ctx8

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Ctx8 p f Ω K K' W S R R' z u)

include C in
theorem img_conj_eq_of_fix {y : G} (hy : y ∈ Subgroup.normalizer (W : Set G))
    (ρ : Thompson.Rep Ω W) (h : conjSub y ρ.K = ρ.K) :
    Thompson.piG W y * ρ.img * (Thompson.piG W y)⁻¹ = ρ.img := by
  rw [← T7D.conjRep_img C.D.c.hΩ hy ρ]
  exact C.D.c.img_eq_of_K_eq _ ρ h

theorem φ_imgQ_mem (ρ : Thompson.Rep Ω W) : C.D.φ (T7D.imgQ ρ) ∈ S4.swaps4 :=
  S4.mem_swaps4_of_isSwap ((C.D.hφ _).mp (T7D.imgQ_mem ρ))

theorem closure_frame_eq_top :
    Subgroup.closure ({T7D.imgQ C.D.F.ρ, T7D.imgQ C.D.F.ρ', T7D.imgQ C.D.F.ρ₃} :
      Set ↥(muGroup Ω W)) = ⊤ := by
  set a := C.D.φ (T7D.imgQ C.D.F.ρ)
  set b := C.D.φ (T7D.imgQ C.D.F.ρ')
  set c := C.D.φ (T7D.imgQ C.D.F.ρ₃)
  have hab : a ≠ b := fun h => C.D.hab (C.D.φ.injective h)
  have hcomm : a * b = b * a := by
    simp only [a, b, ← map_mul, C.D.hcomm]
  have hac : a * c ≠ c * a := by
    intro h
    apply C.D.hac
    apply C.D.φ.injective
    simpa only [a, c, map_mul] using h
  have htop : Subgroup.closure ({a, b, c} : Set (Equiv.Perm (Fin 4))) = ⊤ := by
    rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
    intro t ht
    have ht' := S4.mem_swaps4_of_isSwap ht
    have hmem : ∀ x ∈ ({a, b, c} : Set (Equiv.Perm (Fin 4))),
        x ∈ Subgroup.closure ({a, b, c} : Set (Equiv.Perm (Fin 4))) :=
      fun x hx => Subgroup.subset_closure hx
    have ha := hmem a (by simp)
    have hb := hmem b (by simp)
    have hc := hmem c (by simp)
    rcases S4.swap_word a (C.φ_imgQ_mem _) b (C.φ_imgQ_mem _) c (C.φ_imgQ_mem _) hab hcomm hac t
        ht' with h | h | h | h | h | h <;> rw [h]
    · exact ha
    · exact hb
    · exact hc
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hc) ha
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hb hc) hb
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.mul_mem _ ha hb) hc) hb) ha
  have hmap := congrArg (Subgroup.map C.D.φ.symm.toMonoidHom) htop
  rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ C.D.φ.symm.surjective] at hmap
  rw [← hmap]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨a, Or.inl rfl, by simp [a]⟩
    · exact ⟨b, Or.inr (Or.inl rfl), by simp [b]⟩
    · exact ⟨c, Or.inr (Or.inr rfl), by simp [c]⟩
  · rintro ⟨y, hy | hy | hy, rfl⟩ <;> subst hy <;> simp [a, b, c]

theorem trivMu_of_fix {y : G} (hy : y ∈ Subgroup.normalizer (W : Set G))
    (h₁ : conjSub y C.D.F.ρ.K = C.D.F.ρ.K) (h₂ : conjSub y C.D.F.ρ'.K = C.D.F.ρ'.K)
    (h₃ : conjSub y C.D.F.ρ₃.K = C.D.F.ρ₃.K) : TrivMu Ω W y := by
  set q := Thompson.piG W y
  let Z : Subgroup ↥(muGroup Ω W) :=
    (Subgroup.centralizer ({q} : Set (NQuot (W ⊔ OCW W)))).comap (muGroup Ω W).subtype
  have hmem : ∀ ρ : Thompson.Rep Ω W, conjSub y ρ.K = ρ.K → T7D.imgQ ρ ∈ Z := by
    intro ρ hρ
    show (T7D.imgQ ρ : NQuot (W ⊔ OCW W)) ∈ Subgroup.centralizer ({q} : Set (NQuot (W ⊔ OCW W)))
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := C.img_conj_eq_of_fix hy ρ hρ
    change q * ρ.img * q⁻¹ = ρ.img at h
    change ρ.img * q = q * ρ.img
    calc ρ.img * q = q * ρ.img * q⁻¹ * q := by rw [h]
      _ = q * ρ.img := by group
  have hZ : Z = ⊤ := by
    rw [eq_top_iff, ← C.closure_frame_eq_top, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hmem _ h₁
    · exact hmem _ h₂
    · exact hmem _ h₃
  intro m hm
  have hmN : m ∈ Subgroup.normalizer (W : Set G) := Thompson.MGrp_le_normalizer Ω W hm
  have hmμ : Thompson.piG W m ∈ muGroup Ω W :=
    Thompson.piG_mem_muGroup (Subgroup.mem_sup_left hm)
  have hc : (⟨Thompson.piG W m, hmμ⟩ : ↥(muGroup Ω W)) ∈ Z := hZ ▸ Subgroup.mem_top _
  have hc' : Thompson.piG W m * q = q * Thompson.piG W m :=
    Subgroup.mem_centralizer_singleton_iff.mp hc
  have hx : y * m * y⁻¹ * m⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hmN) (Subgroup.inv_mem _ hy))
      (Subgroup.inv_mem _ hmN)
  rw [← Thompson.piG_eq_one_iff hx, Thompson.piG_mul (Subgroup.mul_mem _
      (Subgroup.mul_mem _ hy hmN) (Subgroup.inv_mem _ hy)) (Subgroup.inv_mem _ hmN),
    Thompson.piG_mul (Subgroup.mul_mem _ hy hmN) (Subgroup.inv_mem _ hy),
    Thompson.piG_mul hy hmN, Thompson.piG_inv hy, Thompson.piG_inv hmN]
  change q * Thompson.piG W m * q⁻¹ * (Thompson.piG W m)⁻¹ = 1
  rw [← hc']
  group

end Ctx8

end S24B

end CFSG.ClassicalInvolution.Asc77
