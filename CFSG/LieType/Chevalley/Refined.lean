module

public import CFSG.LieType.Chevalley.Native
import CFSG.LieType.Chevalley.FixedBruhat
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.BorelTits

theorem eq_and_eq_of_mul_mul_eq {G : Type*} [Group G] {B L U : Subgroup G} (hBL : B ⊓ L = ⊥)
    {g : G} (hconj : ∀ u ∈ U, g * u * g⁻¹ ∈ L) {b b' u u' : G} (hb : b ∈ B) (hb' : b' ∈ B)
    (hu : u ∈ U) (hu' : u' ∈ U) (h : b * g * u = b' * g * u') : b = b' ∧ u = u' := by
  have h1 : b'⁻¹ * b = g * (u' * u⁻¹) * g⁻¹ := by
    calc b'⁻¹ * b = b'⁻¹ * (b * g * u) * u⁻¹ * g⁻¹ := by group
      _ = b'⁻¹ * (b' * g * u') * u⁻¹ * g⁻¹ := by rw [h]
      _ = g * (u' * u⁻¹) * g⁻¹ := by group
  have h2 : b'⁻¹ * b ∈ B ⊓ L := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hb') hb, ?_⟩
    rw [h1]
    exact hconj _ (mul_mem hu' (inv_mem hu))
  rw [hBL, Subgroup.mem_bot, inv_mul_eq_one] at h2
  subst h2
  exact ⟨rfl, mul_left_cancel h⟩

namespace RootGroupData

variable {W Φ ι : Type*} [Group W] [MulAction W Φ] {Rc : RootCombinatorics W Φ ι}
variable {G : Type*} [Group G] {D : RootGroupData Rc G}

theorem conj_mem_iSup_of_smul (m : D.N) {S T : Φ → Prop} (hST : ∀ α, S α → T (D.φ m • α))
    {x : G} (hx : x ∈ ⨆ (α : Φ) (_ : S α), D.X α) :
    (m : G) * x * (m : G)⁻¹ ∈ ⨆ (α : Φ) (_ : T α), D.X α :=
  conj_mem_of_iSup _ (fun α hα _ hy => le_iSup₂_of_le (f := fun (β : Φ) (_ : T β) => D.X β)
    (D.φ m • α) (hST α hα) le_rfl (conj_mem m hy)) hx

theorem exists_mul_rep_mul {Up Um : W → Subgroup G} (n : W → D.N) (hn : ∀ w, D.φ (n w) = w)
    (hcoll : ∀ w, ∀ u ∈ D.U, ∃ p ∈ Up w, ∃ q ∈ Um w, u = p * q)
    (hconj : ∀ m : D.N, ∀ p ∈ Up (D.φ m), (m : G) * p * (m : G)⁻¹ ∈ D.U)
    (m : D.N) {b₁ b₂ : G} (hb₁ : b₁ ∈ D.B) (hb₂ : b₂ ∈ D.B) :
    ∃ b ∈ D.B, ∃ u ∈ Um (D.φ m), b₁ * m * b₂ = b * (n (D.φ m) : G) * u := by
  obtain ⟨h, hh, u, hu, rfl⟩ := exists_mul_of_mem_B hb₂
  obtain ⟨p, hp, q, hq, rfl⟩ := hcoll (D.φ m) u hu
  have hk : ((m * (n (D.φ m))⁻¹ : D.N) : G) ∈ D.H :=
    mem_H_iff.mpr ⟨_, by rw [map_mul, map_inv, hn, mul_inv_cancel], rfl⟩
  refine ⟨b₁ * ((m : G) * h * (m : G)⁻¹) * ((m : G) * p * (m : G)⁻¹) *
      ((m * (n (D.φ m))⁻¹ : D.N) : G), mul_mem (mul_mem (mul_mem hb₁
        (H_le_B (conj_mem_H m hh))) (U_le_B (hconj m p hp))) (H_le_B hk), q, hq, ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem weylHom_eq_of_mem_doubleCoset {M : CoxeterMatrix ι} (cs : CoxeterSystem M W)
    (hcs : ∀ i, cs.simple i = Rc.refl i)
    (hnorm : ∀ i, D.X (Rc.simple i) ≤ Subgroup.normalizer (D.Ui i : Set G))
    (hrank : ∀ i, D.RankOne i) (hBN : ∀ m : D.N, (m : G) ∈ D.B → D.φ m = 1)
    {m m' : D.N} {b₁ b₂ : G} (hb₁ : b₁ ∈ D.B) (hb₂ : b₂ ∈ D.B)
    (h : (m : G) = b₁ * m' * b₂) : D.φ m = D.φ m' := by
  have hφ : ∀ (i : ι) (k : D.N), D.φ (D.n i * k) = cs.simple i * D.φ k := fun i k => by
    rw [map_mul, D.φ_n, hcs]
  have key : ∀ l : ℕ, ∀ m m' : D.N, cs.length (D.φ m) = l →
      cs.length (D.φ m) ≤ cs.length (D.φ m') →
      ∀ c ∈ D.B, ∀ d ∈ D.B, (m : G) = c * m' * d → D.φ m = D.φ m' := by
    intro l
    induction l using Nat.strong_induction_on with
    | _ l ih =>
      intro m m' hl hle c hc d hd h
      by_cases h1 : D.φ m = 1
      ·
        have hmB : (m : G) ∈ D.B := H_le_B (mem_H_iff.mpr ⟨m, h1, rfl⟩)
        have hm' : (m' : G) ∈ D.B := by
          have e : (m' : G) = c⁻¹ * m * d⁻¹ := by rw [h]; group
          rw [e]
          exact mul_mem (mul_mem (inv_mem hc) hmB) (inv_mem hd)
        rw [h1, hBN m' hm']
      obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one h1
      have hi' : cs.length (cs.simple i * D.φ m) + 1 = cs.length (D.φ m) :=
        (cs.length_simple_mul (D.φ m) i).resolve_left fun h' => by
          rw [CoxeterSystem.IsLeftDescent] at hi
          omega
      have hlen := cs.length_simple_mul (D.φ m') i
      have hlt : cs.length (D.φ (D.n i * m)) < l := by
        rw [hφ]
        omega
      rcases exists_simple_mul i (hnorm i) (hrank i) m' hc with
        ⟨c₁, hc₁, c₂, hc₂, he⟩ | ⟨c₁, hc₁, c₂, hc₂, he⟩
      ·
        have e := ih _ hlt (D.n i * m) (D.n i * m') rfl (by rw [hφ, hφ]; omega) c₁ hc₁ (c₂ * d)
          (mul_mem hc₂ hd) (by
            calc ((D.n i * m : D.N) : G) = (D.n i : G) * c * m' * d := by
                  rw [Subgroup.coe_mul, h]
                  group
              _ = c₁ * ((D.n i * m' : D.N) : G) * c₂ * d := by rw [he]
              _ = c₁ * ((D.n i * m' : D.N) : G) * (c₂ * d) := by group)
        rw [hφ, hφ] at e
        exact mul_left_cancel e
      ·
        have e := ih _ hlt (D.n i * m) m' rfl (by rw [hφ]; omega) c₁ hc₁ (c₂ * d)
          (mul_mem hc₂ hd) (by
            calc ((D.n i * m : D.N) : G) = (D.n i : G) * c * m' * d := by
                  rw [Subgroup.coe_mul, h]
                  group
              _ = c₁ * (m' : G) * c₂ * d := by rw [he]
              _ = c₁ * (m' : G) * (c₂ * d) := by group)
        rw [hφ] at e
        have e' := congrArg cs.length e
        omega
  rcases le_total (cs.length (D.φ m)) (cs.length (D.φ m')) with hle | hle
  · exact key _ m m' rfl hle b₁ hb₁ b₂ hb₂ h
  · exact (key _ m' m rfl hle b₁⁻¹ (inv_mem hb₁) b₂⁻¹ (inv_mem hb₂) (by rw [h]; group)).symm

end RootGroupData

section Roots

variable {τ : Tag}

private theorem height_add (u v : Fin τ.rank → ℤ) : height (u + v) = height u + height v := by
  simp only [height, Pi.add_apply, Finset.sum_add_distrib]

private theorem height_nsmul (k : ℕ) (v : Fin τ.rank → ℤ) : height (k • v) = k * height v := by
  simp only [height, Pi.smul_apply, nsmul_eq_mul, Finset.mul_sum]

private theorem height_smul_eq_add {α β γ : Root τ} {a b : ℕ} (h : γ.1 = a • α.1 + b • β.1)
    (w : WeylGroup τ) :
    height (w • γ).1 = a * height (w • α).1 + b * height (w • β).1 := by
  rw [coe_smul_root, coe_smul_root, coe_smul_root, h, smul_add, smul_comm w a, smul_comm w b,
    height_add, height_nsmul, height_nsmul]

private theorem plus_closed (w : WeylGroup τ) (α β γ : Root τ)
    (hα : 0 < height α.1 ∧ 0 < height (w • α).1) (hβ : 0 < height β.1 ∧ 0 < height (w • β).1)
    (h : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • α.1 + b • β.1) :
    0 < height γ.1 ∧ 0 < height (w • γ).1 := by
  obtain ⟨a, b, ha, hb, h⟩ := h
  have h1 := height_smul_eq_add h 1
  have h2 := height_smul_eq_add h w
  simp only [one_smul] at h1
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  obtain ⟨hα1, hα2⟩ := hα
  obtain ⟨hβ1, hβ2⟩ := hβ
  constructor <;> nlinarith

private theorem minus_closed (w : WeylGroup τ) (α β γ : Root τ)
    (hα : 0 < height α.1 ∧ height (w • α).1 < 0) (hβ : 0 < height β.1 ∧ height (w • β).1 < 0)
    (h : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • α.1 + b • β.1) :
    0 < height γ.1 ∧ height (w • γ).1 < 0 := by
  obtain ⟨a, b, ha, hb, h⟩ := h
  have h1 := height_smul_eq_add h 1
  have h2 := height_smul_eq_add h w
  simp only [one_smul] at h1
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  obtain ⟨hα1, hα2⟩ := hα
  obtain ⟨hβ1, hβ2⟩ := hβ
  constructor <;> nlinarith

private theorem simple_smul_simpleRoot (i : Fin τ.rank) :
    simple τ i • simpleRoot τ i = -simpleRoot τ i :=
  (rootCombinatorics τ).refl_simple i

private theorem height_simple_smul_pos {i : Fin τ.rank} {γ : Root τ} (h : 0 < height γ.1)
    (hne : γ ≠ simpleRoot τ i) : 0 < height (simple τ i • γ).1 :=
  (rootCombinatorics τ).pos_refl i γ h hne

private theorem height_simple_smul_neg {i : Fin τ.rank} {γ : Root τ} (h : height γ.1 < 0)
    (hne : γ ≠ -simpleRoot τ i) : height (simple τ i • γ).1 < 0 := by
  have h1 : 0 < height (-γ).1 := by
    rw [coe_neg_root, height_neg]
    omega
  have h2 : -γ ≠ simpleRoot τ i := fun h' => hne (by rw [← h', neg_neg])
  have h3 := height_simple_smul_pos h1 h2
  rw [smul_neg_root, coe_neg_root, height_neg] at h3
  omega

end Roots

section Collection

variable {τ : Tag} {K : Type} [Field K]

theorem X_le_normalizer_iSup_ne {S : Root τ → Prop} (hpos : ∀ α, S α → 0 < height α.1)
    (hS : ∀ α β γ : Root τ, S α → S β →
      (∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • α.1 + b • β.1) → S γ)
    {β : Root τ} (hβ : S β) :
    (nativeRootSubgroups τ K).X β ≤ Subgroup.normalizer
      ((⨆ (α : Root τ) (_ : S α ∧ α ≠ β), (nativeRootSubgroups τ K).X α :
        Subgroup (adjointGroup τ K)) : Set (adjointGroup τ K)) := by
  refine RootGroupData.le_normalizer_of_conj_mem fun x hx u hu => ?_
  refine (iSup₂_le (f := fun (α : Root τ) (_ : S α ∧ α ≠ β) => (nativeRootSubgroups τ K).X α)
    (a := (⨆ (α : Root τ) (_ : S α ∧ α ≠ β), (nativeRootSubgroups τ K).X α).comap
      (MulAut.conj x).toMonoidHom) fun γ hγ y hy => ?_) hu
  have hc := commContained_pos K β γ (hpos β hβ) (hpos γ hγ.1) (Ne.symm hγ.2) x hx y hy
  have hle : (⨆ (δ : Root τ) (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ δ.1 = a • β.1 + b • γ.1),
      (rootOperatorFamily τ).rootSubgroup K δ) ≤
      ⨆ (α : Root τ) (_ : S α ∧ α ≠ β), (nativeRootSubgroups τ K).X α := by
    refine iSup₂_le fun δ hδ => le_iSup₂_of_le (f := fun (α : Root τ) (_ : S α ∧ α ≠ β) =>
      (nativeRootSubgroups τ K).X α) δ ⟨hS β γ δ hβ hγ.1 hδ, fun hδβ => ?_⟩ le_rfl
    obtain ⟨a, b, ha, hb, h⟩ := hδ
    rw [hδβ] at h
    have h1 := congrArg height h
    rw [height_add, height_nsmul, height_nsmul] at h1
    have h2 := hpos β hβ
    have h3 := hpos γ hγ.1
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith
  have hy' : y ∈ ⨆ (α : Root τ) (_ : S α ∧ α ≠ β), (nativeRootSubgroups τ K).X α :=
    le_iSup₂_of_le (f := fun (α : Root τ) (_ : S α ∧ α ≠ β) => (nativeRootSubgroups τ K).X α)
      γ hγ le_rfl hy
  have := mul_mem (hle hc) hy'
  show x * y * x⁻¹ ∈ ⨆ (α : Root τ) (_ : S α ∧ α ≠ β), (nativeRootSubgroups τ K).X α
  simpa [mul_assoc] using this

private theorem iSup_eq_sup_X {S : Root τ → Prop} {β : Root τ} (hβ : S β) :
    (⨆ (α : Root τ) (_ : S α), (nativeRootSubgroups τ K).X α) =
      (⨆ (α : Root τ) (_ : S α ∧ α ≠ β), (nativeRootSubgroups τ K).X α) ⊔
        (nativeRootSubgroups τ K).X β := by
  refine le_antisymm (iSup₂_le fun α hα => ?_) (sup_le (biSup_mono fun α hα => hα.1)
    (le_iSup₂_of_le (f := fun (α : Root τ) (_ : S α) => (nativeRootSubgroups τ K).X α) β hβ
      le_rfl))
  by_cases hαβ : α = β
  · subst hαβ
    exact le_sup_right
  · exact le_sup_of_le_left (le_iSup₂_of_le (f := fun (γ : Root τ) (_ : S γ ∧ γ ≠ β) =>
      (nativeRootSubgroups τ K).X γ) α ⟨hα, hαβ⟩ le_rfl)

theorem exists_mul_mem_X_of_mem_iSup {S : Root τ → Prop} (hpos : ∀ α, S α → 0 < height α.1)
    (hS : ∀ α β γ : Root τ, S α → S β →
      (∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • α.1 + b • β.1) → S γ)
    {β : Root τ} (hβ : S β) {u : adjointGroup τ K}
    (hu : u ∈ ⨆ (α : Root τ) (_ : S α), (nativeRootSubgroups τ K).X α) :
    ∃ v ∈ ⨆ (α : Root τ) (_ : S α ∧ α ≠ β), (nativeRootSubgroups τ K).X α,
      ∃ x ∈ (nativeRootSubgroups τ K).X β, u = v * x := by
  have h : u ∈ (((⨆ (α : Root τ) (_ : S α ∧ α ≠ β), (nativeRootSubgroups τ K).X α) ⊔
      (nativeRootSubgroups τ K).X β : Subgroup (adjointGroup τ K)) : Set (adjointGroup τ K)) := by
    rw [← iSup_eq_sup_X hβ]
    exact hu
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (X_le_normalizer_iSup_ne hpos hS hβ)] at h
  obtain ⟨v, hv, x, hx, rfl⟩ := h
  exact ⟨v, hv, x, hx, rfl⟩

theorem exists_mem_X_mul_of_mem_iSup {S : Root τ → Prop} (hpos : ∀ α, S α → 0 < height α.1)
    (hS : ∀ α β γ : Root τ, S α → S β →
      (∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • α.1 + b • β.1) → S γ)
    {β : Root τ} (hβ : S β) {u : adjointGroup τ K}
    (hu : u ∈ ⨆ (α : Root τ) (_ : S α), (nativeRootSubgroups τ K).X α) :
    ∃ x ∈ (nativeRootSubgroups τ K).X β,
      ∃ v ∈ ⨆ (α : Root τ) (_ : S α ∧ α ≠ β), (nativeRootSubgroups τ K).X α, u = x * v := by
  have h : u ∈ (((nativeRootSubgroups τ K).X β ⊔
      ⨆ (α : Root τ) (_ : S α ∧ α ≠ β), (nativeRootSubgroups τ K).X α :
        Subgroup (adjointGroup τ K)) : Set (adjointGroup τ K)) := by
    rw [sup_comm, ← iSup_eq_sup_X hβ]
    exact hu
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (X_le_normalizer_iSup_ne hpos hS hβ)] at h
  obtain ⟨x, hx, v, hv, rfl⟩ := h
  exact ⟨x, hx, v, hv, rfl⟩

private theorem mem_iSup_X_of_imp {S T : Root τ → Prop} (hST : ∀ α, S α → T α)
    {x : adjointGroup τ K} (hx : x ∈ ⨆ (α : Root τ) (_ : S α), (nativeRootSubgroups τ K).X α) :
    x ∈ ⨆ (α : Root τ) (_ : T α), (nativeRootSubgroups τ K).X α :=
  biSup_mono (f := fun α => (nativeRootSubgroups τ K).X α) hST hx

private theorem mem_iSup_X_of_mem {T : Root τ → Prop} {β : Root τ} (hβ : T β)
    {x : adjointGroup τ K} (hx : x ∈ (nativeRootSubgroups τ K).X β) :
    x ∈ ⨆ (α : Root τ) (_ : T α), (nativeRootSubgroups τ K).X α :=
  le_iSup₂_of_le (f := fun (α : Root τ) (_ : T α) => (nativeRootSubgroups τ K).X α) β hβ le_rfl
    hx

variable [Finite K]

theorem exists_mem_Uplus_mem_Uminus (w : WeylGroup τ) {u : adjointGroup τ K}
    (hu : u ∈ (nativeData τ K).U) :
    ∃ u₁ ∈ Uplus τ K w, ∃ u₂ ∈ Uminus τ K w, u = u₁ * u₂ := by
  induction w using (coxeterSystem τ).simple_induction_left with
  | one =>
    refine ⟨u, mem_iSup_X_of_imp (S := fun α : Root τ => 0 < height α.1)
      (T := fun α : Root τ => 0 < height α.1 ∧ 0 < height ((1 : WeylGroup τ) • α).1)
      (fun α hα => ⟨hα, by rwa [one_smul]⟩) hu, 1, one_mem _, (mul_one u).symm⟩
  | mul_simple_left w i ih =>
    obtain ⟨p, hp, q, hq, rfl⟩ := ih
    have hsw : ∀ α : Root τ, ((coxeterSystem τ).simple i * w) • α = simple τ i • (w • α) :=
      fun α => mul_smul _ _ _
    have hsimple : height (simpleRoot τ i).1 = 1 := height_single i
    rcases IsRoot.height_pos_or_neg (w⁻¹ • simpleRoot τ i).2 with hA | hB
    ·
      have hwβ : w • (w⁻¹ • simpleRoot τ i) = simpleRoot τ i := smul_inv_smul w _
      obtain ⟨p', hp', x, hx, rfl⟩ := exists_mul_mem_X_of_mem_iSup
        (S := fun α : Root τ => 0 < height α.1 ∧ 0 < height (w • α).1) (fun _ h => h.1)
        (plus_closed w) (β := w⁻¹ • simpleRoot τ i) ⟨hA, by rw [hwβ, hsimple]; exact one_pos⟩ hp
      refine ⟨p', mem_iSup_X_of_imp (fun α hα => ⟨hα.1.1, ?_⟩) hp', x * q,
        mul_mem (mem_iSup_X_of_mem ⟨hA, ?_⟩ hx) (mem_iSup_X_of_imp (fun α hα => ⟨hα.1, ?_⟩) hq),
        by rw [mul_assoc]⟩
      · rw [hsw]
        exact height_simple_smul_pos hα.1.2 fun h => hα.2 (smul_left_cancel w (h.trans hwβ.symm))
      · rw [hsw, hwβ, simple_smul_simpleRoot, coe_neg_root, height_neg, hsimple]
        norm_num
      · rw [hsw]
        refine height_simple_smul_neg hα.2 fun h => ?_
        have e : α = -(w⁻¹ • simpleRoot τ i) :=
          smul_left_cancel w (by rw [h, smul_neg_root, hwβ])
        have h1 := hα.1
        rw [e, coe_neg_root, height_neg] at h1
        omega
    ·
      have hwβ : w • -(w⁻¹ • simpleRoot τ i) = -simpleRoot τ i := by
        rw [smul_neg_root, smul_inv_smul]
      have hβ : 0 < height (-(w⁻¹ • simpleRoot τ i)).1 := by
        rw [coe_neg_root, height_neg]
        omega
      obtain ⟨x, hx, q', hq', rfl⟩ := exists_mem_X_mul_of_mem_iSup
        (S := fun α : Root τ => 0 < height α.1 ∧ height (w • α).1 < 0) (fun _ h => h.1)
        (minus_closed w) (β := -(w⁻¹ • simpleRoot τ i))
        ⟨hβ, by rw [hwβ, coe_neg_root, height_neg, hsimple]; norm_num⟩ hq
      refine ⟨p * x, mul_mem (mem_iSup_X_of_imp (fun α hα => ⟨hα.1, ?_⟩) hp)
        (mem_iSup_X_of_mem ⟨hβ, ?_⟩ hx), q', mem_iSup_X_of_imp (fun α hα => ⟨hα.1.1, ?_⟩) hq',
        by rw [mul_assoc]⟩
      · rw [hsw]
        refine height_simple_smul_pos hα.2 fun h => ?_
        have e : α = w⁻¹ • simpleRoot τ i := by rw [← h, inv_smul_smul]
        have h1 := hα.1
        rw [e] at h1
        omega
      · rw [hsw, hwβ, smul_neg_root, simple_smul_simpleRoot, neg_neg, hsimple]
        exact one_pos
      · rw [hsw]
        exact height_simple_smul_neg hα.1.2 fun h => hα.2 (smul_left_cancel w (h.trans hwβ.symm))

end Collection

section Triangular

variable {τ : Tag} {K : Type} [Field K]

variable (τ K) in
@[expose] noncomputable def Uneg : Subgroup (adjointGroup τ K) :=
  ⨆ (α : Root τ) (_ : height α.1 < 0), (nativeRootSubgroups τ K).X α

private noncomputable def htWt (a : Label τ) : ℝ :=
  (height (labelWt τ a) : ℝ)

private theorem repr_glRep_sub_one (g : adjointGroup τ K) (a b : Label τ) :
    Finsupp.basisSingleOne.repr ((glRep (adjointGroup τ K) g - 1) (Finsupp.basisSingleOne b)) a =
      ((g : ModGL τ K) : Module.End K (RootModule τ K)) (Finsupp.single b 1) a -
        (Finsupp.single b 1 : RootModule τ K) a := by
  simp only [Finsupp.coe_basisSingleOne, Finsupp.basisSingleOne_repr, LinearEquiv.refl_apply,
    LinearMap.sub_apply, Module.End.one_apply, glRep_apply, Finsupp.coe_sub, Pi.sub_apply]

private theorem repr_glRep (g : adjointGroup τ K) (a b : Label τ) :
    Finsupp.basisSingleOne.repr (glRep (adjointGroup τ K) g (Finsupp.basisSingleOne b)) a =
      ((g : ModGL τ K) : Module.End K (RootModule τ K)) (Finsupp.single b 1) a := by
  simp only [Finsupp.coe_basisSingleOne, Finsupp.basisSingleOne_repr, LinearEquiv.refl_apply,
    glRep_apply]

private theorem raises_of_mem_X {α : Root τ} {x : adjointGroup τ K}
    (hx : x ∈ (nativeRootSubgroups τ K).X α) {v : ℝ} (hv : 0 ≤ v * height α.1) :
    Weighted.Raises Finsupp.basisSingleOne htWt v (v * height α.1)
      (glRep (adjointGroup τ K) x - 1) := by
  intro a b hab
  rw [repr_glRep_sub_one] at hab
  obtain ⟨k, hk, hw⟩ := (nativeRootSubgroups τ K).weight_shift α x hx a b hab
  simp only [Real.inner_apply, htWt, hw, height_add, height_nsmul]
  push_cast
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

variable [Finite K]

private theorem U_le_gradedKernel :
    (nativeData τ K).U ≤
      Weighted.gradedKernel Finsupp.basisSingleOne htWt (glRep (adjointGroup τ K)) 1 := by
  refine iSup₂_le fun α (hα : 0 < height α.1) x hx => ?_
  have hα' : (0 : ℝ) < height α.1 := by exact_mod_cast hα
  exact ⟨_, by linarith, raises_of_mem_X hx (by linarith)⟩

private theorem Uneg_le_gradedKernel :
    Uneg τ K ≤
      Weighted.gradedKernel Finsupp.basisSingleOne htWt (glRep (adjointGroup τ K)) (-1) := by
  refine iSup₂_le fun α (hα : height α.1 < 0) x hx => ?_
  have hα' : (height α.1 : ℝ) < 0 := by exact_mod_cast hα
  exact ⟨_, by linarith, raises_of_mem_X hx (by linarith)⟩

private theorem B_le_triangular :
    (nativeData τ K).B ≤
      Weighted.triangular Finsupp.basisSingleOne htWt (glRep (adjointGroup τ K)) 1 := by
  refine sup_le (fun h hh => ?_)
    (U_le_gradedKernel.trans (Weighted.gradedKernel_le_triangular _ 1))
  obtain ⟨k, hk, rfl⟩ := (RootGroupData.mem_H_iff (D := nativeData τ K)).mp hh
  refine (Weighted.mem_triangular _).mpr fun a b hab => ?_
  have hmono := isMonomial_weylHom k a b hab
  change weylHom τ K k = 1 at hk
  rw [hk, one_smul] at hmono
  simp only [Real.inner_apply, htWt, hmono, add_zero, le_refl]

theorem height_lt_of_mem_U {u : adjointGroup τ K} (hu : u ∈ (nativeData τ K).U) {a b : Label τ}
    (h : ((u : ModGL τ K) : Module.End K (RootModule τ K)) (Finsupp.single b 1) a -
      (Finsupp.single b 1 : RootModule τ K) a ≠ 0) :
    height (labelWt τ b) < height (labelWt τ a) := by
  obtain ⟨c, hc, hr⟩ := U_le_gradedKernel hu
  have h1 := hr a b (by rwa [repr_glRep_sub_one])
  simp only [Real.inner_apply, htWt, mul_one] at h1
  exact_mod_cast (by linarith : (height (labelWt τ b) : ℝ) < height (labelWt τ a))

theorem height_lt_of_mem_Uneg {u : adjointGroup τ K} (hu : u ∈ Uneg τ K) {a b : Label τ}
    (h : ((u : ModGL τ K) : Module.End K (RootModule τ K)) (Finsupp.single b 1) a -
      (Finsupp.single b 1 : RootModule τ K) a ≠ 0) :
    height (labelWt τ a) < height (labelWt τ b) := by
  obtain ⟨c, hc, hr⟩ := Uneg_le_gradedKernel hu
  have h1 := hr a b (by rwa [repr_glRep_sub_one])
  simp only [Real.inner_apply, htWt, mul_neg, mul_one] at h1
  exact_mod_cast (by linarith : (height (labelWt τ a) : ℝ) < height (labelWt τ b))

theorem height_le_of_mem_B {g : adjointGroup τ K} (hg : g ∈ (nativeData τ K).B) {a b : Label τ}
    (h : ((g : ModGL τ K) : Module.End K (RootModule τ K)) (Finsupp.single b 1) a ≠ 0) :
    height (labelWt τ b) ≤ height (labelWt τ a) := by
  have h1 := (Weighted.mem_triangular _).mp (B_le_triangular hg) a b (by rwa [repr_glRep])
  simp only [Real.inner_apply, htWt, mul_one, add_zero] at h1
  exact_mod_cast h1

variable (τ K) in
theorem nativeData_B_inf_Uneg : (nativeData τ K).B ⊓ Uneg τ K = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxB, hxU⟩
  rw [Subgroup.mem_bot]
  apply glRep_injective (adjointGroup τ K)
  rw [map_one, ← sub_eq_zero]
  refine eq_zero_of_repr_eq_zero Finsupp.basisSingleOne fun a b => ?_
  rw [repr_glRep_sub_one]
  by_contra hab
  have h1 := height_lt_of_mem_Uneg hxU hab
  by_cases hba : b = a
  · subst hba
    omega
  · rw [Finsupp.single_eq_of_ne' hba, sub_zero] at hab
    have h2 := height_le_of_mem_B hxB hab
    omega

theorem weylHom_eq_one_of_mem_B (m : monomialGroup τ K)
    (hm : (m : adjointGroup τ K) ∈ (nativeData τ K).B) : weylHom τ K m = 1 := by
  refine rootCombinatorics_eq_one fun i => ?_
  by_contra hneg
  have hlt : height (weylHom τ K m • simpleRoot τ i).1 < 0 :=
    lt_of_le_of_ne (not_lt.mp hneg) (weylHom τ K m • simpleRoot τ i).2.height_ne_zero
  have hle : (nativeRootSubgroups τ K).X (weylHom τ K m • simpleRoot τ i) ≤
      (nativeData τ K).B ⊓ Uneg τ K := by
    rw [← (nativeRootSubgroups τ K).map_conj m (simpleRoot τ i)]
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hm ((nativeData τ K).U_le_B
      ((nativeData τ K).simple_le_U i hx))) (inv_mem hm), ?_⟩
    exact le_iSup₂_of_le (f := fun (β : Root τ) (_ : height β.1 < 0) =>
      (nativeRootSubgroups τ K).X β) _ hlt le_rfl
      (RootGroupData.conj_mem (D := nativeData τ K) m hx)
  rw [nativeData_B_inf_Uneg] at hle
  exact (nativeRootSubgroups τ K).X_ne_bot _ (le_bot_iff.mp hle)

end Triangular

section Conjugation

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem conj_mem_U_of_mem_Uplus (m : monomialGroup τ K) {x : adjointGroup τ K}
    (hx : x ∈ Uplus τ K (weylHom τ K m)) :
    (m : adjointGroup τ K) * x * (m : adjointGroup τ K)⁻¹ ∈ (nativeData τ K).U :=
  RootGroupData.conj_mem_iSup_of_smul (D := nativeData τ K) m
    (S := fun α => 0 < height α.1 ∧ 0 < height (weylHom τ K m • α).1)
    (T := fun α => (rootCombinatorics τ).pos α) (fun _ hα => hα.2) hx

theorem conj_mem_Uneg_of_mem_Uminus (m : monomialGroup τ K) {x : adjointGroup τ K}
    (hx : x ∈ Uminus τ K (weylHom τ K m)) :
    (m : adjointGroup τ K) * x * (m : adjointGroup τ K)⁻¹ ∈ Uneg τ K :=
  RootGroupData.conj_mem_iSup_of_smul (D := nativeData τ K) m
    (S := fun α => 0 < height α.1 ∧ height (weylHom τ K m • α).1 < 0)
    (T := fun α => height α.1 < 0) (fun _ hα => hα.2) hx

theorem nrep_conj_mem_U {w : WeylGroup τ} {x : adjointGroup τ K} (hx : x ∈ Uplus τ K w) :
    nrep τ K w * x * (nrep τ K w)⁻¹ ∈ (nativeData τ K).U :=
  conj_mem_U_of_mem_Uplus ⟨nrep τ K w, nrep_mem_monomialGroup τ K w⟩
    (by rwa [weylHom_nrep])

theorem nrep_conj_mem_Uneg {w : WeylGroup τ} {x : adjointGroup τ K} (hx : x ∈ Uminus τ K w) :
    nrep τ K w * x * (nrep τ K w)⁻¹ ∈ Uneg τ K :=
  conj_mem_Uneg_of_mem_Uminus ⟨nrep τ K w, nrep_mem_monomialGroup τ K w⟩
    (by rwa [weylHom_nrep])

end Conjugation

section Bruhat

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem nativeData_exists_mem_doubleCoset (g : adjointGroup τ K) :
    ∃ m : monomialGroup τ K, ∃ b₁ ∈ (nativeData τ K).B, ∃ b₂ ∈ (nativeData τ K).B,
      g = b₁ * (m : adjointGroup τ K) * b₂ :=
  RootGroupData.exists_mem_doubleCoset (D := nativeData τ K)
    (nativeRootSubgroups τ K).simple_le_normalizer_Ui (nativeRootSubgroups τ K).rankOne
    (nativeRootSubgroups τ K).closure_B_union_n g

theorem nativeData_weylHom_eq_of_mul_eq (m m' : monomialGroup τ K) {b₁ b₂ b₃ b₄ : adjointGroup τ K}
    (hb₁ : b₁ ∈ (nativeData τ K).B) (hb₂ : b₂ ∈ (nativeData τ K).B)
    (hb₃ : b₃ ∈ (nativeData τ K).B) (hb₄ : b₄ ∈ (nativeData τ K).B)
    (h : b₁ * (m : adjointGroup τ K) * b₂ = b₃ * (m' : adjointGroup τ K) * b₄) :
    weylHom τ K m = weylHom τ K m' :=
  RootGroupData.weylHom_eq_of_mem_doubleCoset (D := nativeData τ K) (coxeterSystem τ)
    (fun _ => rfl) (nativeRootSubgroups τ K).simple_le_normalizer_Ui
    (nativeRootSubgroups τ K).rankOne weylHom_eq_one_of_mem_B (mul_mem (inv_mem hb₁) hb₃)
    (mul_mem hb₄ (inv_mem hb₂)) (by
      calc (m : adjointGroup τ K) = b₁⁻¹ * (b₁ * m * b₂) * b₂⁻¹ := by group
        _ = b₁⁻¹ * (b₃ * m' * b₄) * b₂⁻¹ := by rw [h]
        _ = b₁⁻¹ * b₃ * m' * (b₄ * b₂⁻¹) := by group)

theorem nativeData_exists_mul_nrep_mul (m : monomialGroup τ K) {b₁ b₂ : adjointGroup τ K}
    (hb₁ : b₁ ∈ (nativeData τ K).B) (hb₂ : b₂ ∈ (nativeData τ K).B) :
    ∃ b ∈ (nativeData τ K).B, ∃ u ∈ Uminus τ K (weylHom τ K m),
      b₁ * (m : adjointGroup τ K) * b₂ = b * nrep τ K (weylHom τ K m) * u :=
  RootGroupData.exists_mul_rep_mul (D := nativeData τ K) (Up := Uplus τ K) (Um := Uminus τ K)
    (fun w => ⟨nrep τ K w, nrep_mem_monomialGroup τ K w⟩) (weylHom_nrep τ K)
    (fun w _ hu => exists_mem_Uplus_mem_Uminus w hu) (fun m _ hp => conj_mem_U_of_mem_Uplus m hp)
    m hb₁ hb₂

theorem nativeData_eq_of_mul_nrep_mul_eq (w : WeylGroup τ) {b b' u u' : adjointGroup τ K}
    (hb : b ∈ (nativeData τ K).B) (hb' : b' ∈ (nativeData τ K).B) (hu : u ∈ Uminus τ K w)
    (hu' : u' ∈ Uminus τ K w) (h : b * nrep τ K w * u = b' * nrep τ K w * u') :
    b = b' ∧ u = u' :=
  eq_and_eq_of_mul_mul_eq (nativeData_B_inf_Uneg τ K) (fun _ hx => nrep_conj_mem_Uneg hx) hb hb'
    hu hu' h

variable (τ K) in
theorem native_refined_bruhat :
    (∀ g : adjointGroup τ K, ∃ m : monomialGroup τ K, ∃ b₁ ∈ (nativeData τ K).B,
      ∃ b₂ ∈ (nativeData τ K).B, g = b₁ * (m : adjointGroup τ K) * b₂) ∧
    (∀ m m' : monomialGroup τ K, ∀ b₁ ∈ (nativeData τ K).B, ∀ b₂ ∈ (nativeData τ K).B,
      ∀ b₃ ∈ (nativeData τ K).B, ∀ b₄ ∈ (nativeData τ K).B,
      b₁ * (m : adjointGroup τ K) * b₂ = b₃ * (m' : adjointGroup τ K) * b₄ →
        weylHom τ K m = weylHom τ K m') ∧
    (∀ m : monomialGroup τ K, ∀ b₁ ∈ (nativeData τ K).B, ∀ b₂ ∈ (nativeData τ K).B,
      ∃ b ∈ (nativeData τ K).B,
        ∃ u ∈ (Uminus τ K (weylHom τ K m) : Set (adjointGroup τ K)),
          b₁ * (m : adjointGroup τ K) * b₂ = b * nrep τ K (weylHom τ K m) * u) ∧
    (∀ w : WeylGroup τ, ∀ b ∈ (nativeData τ K).B, ∀ b' ∈ (nativeData τ K).B,
      ∀ u ∈ (Uminus τ K w : Set (adjointGroup τ K)),
      ∀ u' ∈ (Uminus τ K w : Set (adjointGroup τ K)),
        b * nrep τ K w * u = b' * nrep τ K w * u' → b = b' ∧ u = u') :=
  ⟨nativeData_exists_mem_doubleCoset,
    fun m m' _ hb₁ _ hb₂ _ hb₃ _ hb₄ h => nativeData_weylHom_eq_of_mul_eq m m' hb₁ hb₂ hb₃ hb₄ h,
    fun m _ hb₁ _ hb₂ => nativeData_exists_mul_nrep_mul m hb₁ hb₂,
    fun w _ hb _ hb' _ hu _ hu' h => nativeData_eq_of_mul_nrep_mul_eq w hb hb' hu hu' h⟩

theorem nativeData_exists_fixed_mul (F : adjointGroup τ K ≃* adjointGroup τ K)
    (δ : WeylGroup τ ≃* WeylGroup τ)
    (hFB : ∀ b ∈ (nativeData τ K).B, F b ∈ (nativeData τ K).B)
    (hFN : ∀ m : monomialGroup τ K, F m ∈ monomialGroup τ K)
    (hδ : ∀ m : monomialGroup τ K, weylHom τ K ⟨F m, hFN m⟩ = δ (weylHom τ K m))
    (hFU : ∀ w, ∀ u ∈ Uminus τ K w, F u ∈ Uminus τ K (δ w))
    (hFn : ∀ w, δ w = w → F (nrep τ K w) = nrep τ K w) {g : adjointGroup τ K} (hg : F g = g) :
    ∃ w, δ w = w ∧ ∃ b ∈ (nativeData τ K).B, F b = b ∧ ∃ u ∈ Uminus τ K w, F u = u ∧
      g = b * nrep τ K w * u := by
  obtain ⟨hcover, hdisj, hexists, hunique⟩ := native_refined_bruhat τ K
  exact exists_fixed_mul_of_fixed (nativeData τ K).B (monomialGroup τ K) (weylHom τ K)
    (nrep τ K) (fun w => (Uminus τ K w : Set (adjointGroup τ K))) F δ hcover hdisj hexists
    hunique hFB hFN hδ hFU hFn hg

end Bruhat

end CFSG.LieType.Chevalley
