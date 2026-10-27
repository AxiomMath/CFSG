module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBIdx4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBSub6

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42 CFSG.ComponentClassification.J2Cover CFSG.Sporadic.Schreier
open scoped commutatorElement

namespace EndB

section MZ

variable {G : Type*} [Group G]

@[expose] def MZ (z g d : G) : Prop := g * d * g⁻¹ = d ∨ g * d * g⁻¹ = d * z

theorem MZ.of_comm {z g d : G} (h : g * d = d * g) : MZ z g d :=
  Or.inl (by rw [h, mul_inv_cancel_right])

theorem MZ.mul_right {z g d₁ d₂ : G} (hz2 : z * z = 1) (hzd : d₂ * z = z * d₂)
    (h₁ : MZ z g d₁) (h₂ : MZ z g d₂) : MZ z g (d₁ * d₂) := by
  have h : g * (d₁ * d₂) * g⁻¹ = (g * d₁ * g⁻¹) * (g * d₂ * g⁻¹) := by group
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> rw [MZ, h, h₁, h₂]
  · exact Or.inl rfl
  · exact Or.inr (by group)
  · right
    rw [mul_assoc d₁ z d₂, ← hzd]
    group
  · left
    calc d₁ * z * (d₂ * z) = d₁ * (z * d₂) * z := by group
      _ = d₁ * (d₂ * z) * z := by rw [hzd]
      _ = d₁ * d₂ * (z * z) := by group
      _ = d₁ * d₂ := by rw [hz2, mul_one]

theorem MZ.mul_left {z g₁ g₂ d : G} (hz2 : z * z = 1) (hgz : g₁ * z = z * g₁)
    (h₁ : MZ z g₁ d) (h₂ : MZ z g₂ d) : MZ z (g₁ * g₂) d := by
  have hgz' : g₁ * z * g₁⁻¹ = z := by rw [hgz, mul_inv_cancel_right]
  have h : g₁ * g₂ * d * (g₁ * g₂)⁻¹ = g₁ * (g₂ * d * g₂⁻¹) * g₁⁻¹ := by group
  rcases h₂ with h₂ | h₂
  · rw [MZ, h, h₂]
    exact h₁
  · rw [MZ, h, h₂]
    have h3 : g₁ * (d * z) * g₁⁻¹ = (g₁ * d * g₁⁻¹) * (g₁ * z * g₁⁻¹) := by group
    rw [h3, hgz']
    rcases h₁ with h₁ | h₁ <;> rw [h₁]
    · exact Or.inr rfl
    · left
      rw [mul_assoc, hz2, mul_one]

theorem MZ.swap {z x d : G} (hxz : x * z = z * x) (h : MZ z x d⁻¹) :
    d * x * d⁻¹ = x ∨ d * x * d⁻¹ = x * z := by
  have e : d * x * d⁻¹ = d * (x * d⁻¹ * x⁻¹) * x := by group
  rcases h with h | h <;> rw [e, h]
  · left
    group
  · right
    rw [hxz]
    group

end MZ

theorem false_of_inv {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ}
    {S : Subgroup X} {w z : X} {V : Subgroup X} {i j : ℕ}
    (hs : Setting46e t L p f S w z V i j) {W W₁ : Subgroup X}
    (hTW : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ W) (hWW₁ : W ≤ W₁) (hW₁ : IsPGroup 2 W₁)
    {x : X} (hxW₁ : x ∈ W₁) (hxW : x ∉ W) (hxt : x * t = t * x) (hx2 : x * x = 1)
    (hxz : x * z = z * x) (hzD : ∀ d ∈ S ⊓ L, d * z = z * d)
    (hxd : ∀ d ∈ S ⊓ L, d * x * d⁻¹ = x ∨ d * x * d⁻¹ = x * z) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTt : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ centralizer ({t} : Set X) :=
    hs.lemma45.isSylowOf_T.le.trans inf_le_left
  have hxC : x ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr hxt
  have hle : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ⊔ zpowers x ≤ centralizer ({t} : Set X) :=
    sup_le hTt (zpowers_le.mpr hxC)
  have h2 : IsPGroup 2 ↥(zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ⊔ zpowers x) :=
    hW₁.to_le (sup_le (hTW.trans hWW₁) (zpowers_le.mpr hxW₁))
  obtain ⟨S', hS', hS'le⟩ := exists_isSylowOf_ge h2 hle
  obtain ⟨-, -, -, hF⟩ := hs.setup.sylow_transport hS' (le_sup_left.trans hS'le)
  have hDT : S ⊓ L ≤ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := le_sup_right.trans le_sup_left
  have hz2 : z ^ 2 = 1 := by rw [← hs.setup.z_order]; exact pow_orderOf_eq_one z
  have hx2' : x ^ 2 = 1 := by rw [sq]; exact hx2
  have hFle : closure ({x, z} : Set X) ≤ closure {t, w ^ (orderOf w / 2), z} := by
    refine hF _ ?_ ?_ ?_
    · rw [closure_le]
      rintro _ (rfl | rfl)
      · exact hS'le (mem_sup_right (mem_zpowers _))
      · exact hS'le (mem_sup_left (hDT hs.setup.z_mem))
    · intro g hg y hy
      have hcl : closure ({x, z} : Set X) ≤
          (closure ({x, z} : Set X)).comap (MulAut.conj g).toMonoidHom := by
        rw [closure_le]
        rintro _ (rfl | rfl)
        · rw [SetLike.mem_coe, mem_comap]
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          rcases hxd g hg with h | h <;> rw [h]
          · exact subset_closure (Set.mem_insert _ _)
          · exact mul_mem (subset_closure (Set.mem_insert _ _))
              (subset_closure (Set.mem_insert_of_mem _ rfl))
        · rw [SetLike.mem_coe, mem_comap]
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          rw [hzD g hg, mul_inv_cancel_right]
          exact subset_closure (Set.mem_insert_of_mem _ rfl)
      have := hcl hy
      rw [mem_comap] at this
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this
    · intro y hy
      rcases mem_closure_pair hx2' hz2 hxz hy with rfl | rfl | rfl | rfl
      · exact one_pow 2
      · exact hx2'
      · exact hz2
      · rw [(show Commute x z from hxz).mul_pow, hx2', hz2, one_mul]
  exact hxW (hTW (hs.setup.X_le_T (hFle (subset_closure (Set.mem_insert x _)))))

end EndB

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.JLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* P}

theorem count_ge
    (hKC : AutPSL2CentralizerInput) (hJ : JLayer hs π)
    (hπi : Function.Injective π)
    (hQ : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    (hcent : Nat.card ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
      centralizer {hs.setup.tBar i j}) = 336) {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hUW : V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ≤ W) {e' : ℕ → X}
    (h' : IdxModel 128 e' vT vI 0) (hsub : h'.sub = W ⊓ oP W) {v₀ : ℕ} (hv₀ : v₀ < 128)
    (hte : ∀ k < 128, t * e' k * t⁻¹ = e' (vAc v₀ k)) :
    16 ≤ (List.range 128).countP (fun d => vAc v₀ d == d) := by
  classical
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  have hT64 : Nat.card ↥(zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) = 64 := hJ.card_T hcent
  have hTW : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ W := hs.beta.lt.le.trans hUW
  have hTt : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ centralizer ({t} : Set X) :=
    hs.lemma45.isSylowOf_T.le.trans inf_le_left
  have htC : t ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr rfl
  have hβC : β ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (hs.setup.t_mem_centralizer_beta i j)).symm
  have hcu₀ := vCu_facts
  let Cn := {d : ℕ // d ∈ List.range 128 ∧ (vAc v₀ d == d) = true}
  have hCn : Nat.card Cn = (List.range 128).countP (fun d => vAc v₀ d == d) :=
    card_subtype_mem_countP List.nodup_range _
  have : Finite Cn := Finite.of_injective (fun d : Cn => (⟨d.1, List.mem_range.mp d.2.1⟩ : Fin 128))
    (fun a b h => Subtype.ext (by simpa using congrArg Fin.val h))
  let ε : Fin 4 → X := ![1, t, β, β * t]
  have hεC : ∀ k, ε k ∈ centralizer ({t} : Set X) := by
    intro k
    fin_cases k
    · exact one_mem _
    · exact htC
    · exact hβC
    · exact mul_mem hβC htC
  let F : Cn × Fin 4 → ↥(zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) := fun q =>
    if h : e' q.1.1 * ε q.2 ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w then ⟨_, h⟩ else 1
  have hF : Function.Surjective F := by
    rintro ⟨x, hx⟩
    obtain ⟨v, hv, hcases⟩ := hJ.exists_V0_mul hKC hπi hQ hW hUW (hTW hx)
    obtain ⟨m, hm, rfl⟩ : ∃ m < 128, e' m = v := by rw [← hsub] at hv; exact hv
    obtain ⟨k, hk⟩ : ∃ k, x = e' m * ε k := by
      rcases hcases with h | h | h | h
      · exact ⟨0, by rw [h]; simp [ε]⟩
      · exact ⟨1, by rw [h]; simp [ε]⟩
      · exact ⟨2, by rw [h]; simp [ε, hβ]⟩
      · exact ⟨3, by rw [h]; simp [ε, hβ]⟩
    have hmC : e' m ∈ centralizer ({t} : Set X) := by
      rw [show e' m = x * (ε k)⁻¹ by rw [hk]; group]
      exact mul_mem (hTt hx) (inv_mem (hεC k))
    have hfix : vAc v₀ m = m := by
      have hlt : vAc v₀ m < 128 :=
        vModel.T_lt _ (vModel.T_lt _ hv₀ _ (hcu₀ m hm).1) _ (vModel.I_lt _ hv₀)
      refine h'.inj _ hlt _ hm ?_
      rw [← hte m hm, ← mem_centralizer_singleton_iff.mp hmC, mul_inv_cancel_right]
    refine ⟨(⟨m, List.mem_range.mpr hm, by rw [hfix]; exact beq_self_eq_true m⟩, k), ?_⟩
    have hxT : e' m * ε k ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := hk ▸ hx
    simp only [F, hxT, ↓reduceDIte]
    exact Subtype.ext hk.symm
  have h1 := Nat.card_le_card_of_surjective F hF
  rw [Nat.card_prod, hCn, hT64, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin] at h1
  omega

end EndB.JLayer

end CFSG.ComponentClassification.HarrisLit
