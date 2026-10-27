module

public import CFSG.CGT.PushingUpLit.SYMB.FiveStrict
public import CFSG.CGT.PushingUpLit.SYMB.FiveMult
public import CFSG.CGT.PushingUpLit.SYMB.FiveReduce

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7 Equiv
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ}
  {φ : ↥G →* Equiv.Perm (Fin 5)} {ψ : ↥V →* ↥(G6.coreMod 5)} {T' : Set (Equiv.Perm (Fin 5))}
  {S : SymSetting G T V 5 φ ψ T'} {V₁ E : Subgroup Γ} {a b c d : Fin 5}

omit [Finite Γ] in
theorem V₁_le_sup_Cfix (hV : V1Iso S V₁) (hp : Pts G T φ a b c d) :
    V₁ ≤ Cfix ψ V₁ (Subgroup.zpowers (swap a b)) ⊔ Cfix ψ V₁ (Subgroup.zpowers (swap c d)) := by
  intro v hv
  have hvV : v ∈ V := hV.le hv
  have htop := Delta5Swaps.sup_Fixed_eq_top hp.hab hp.hcd hp.hac hp.had hp.hbc hp.hbd
  have hψv : ψ ⟨v, hvV⟩ ∈ Delta5Swaps.Fixed (Subgroup.zpowers (swap a b)) ⊔
      Delta5Swaps.Fixed (Subgroup.zpowers (swap c d)) := by
    rw [htop]
    trivial
  obtain ⟨w₁, hw₁, w₂, hw₂, hw⟩ := Subgroup.mem_sup.1 hψv
  obtain ⟨v₁, hv₁, hψ₁⟩ := hV.surj w₁
  obtain ⟨v₂, hv₂, hψ₂⟩ := hV.surj w₂
  have e : ψ ⟨(v₁ : Γ) * (v₂ : Γ), V.mul_mem v₁.2 v₂.2⟩ = ψ ⟨v, hvV⟩ := by
    have : (⟨(v₁ : Γ) * (v₂ : Γ), V.mul_mem v₁.2 v₂.2⟩ : ↥V) = v₁ * v₂ := rfl
    rw [this, map_mul, hψ₁, hψ₂]
    exact hw
  have hv12 : v = (v₁ : Γ) * (v₂ : Γ) :=
    hV.eq_of_psi_eq hv (V₁.mul_mem hv₁ hv₂) e.symm
  rw [hv12]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left (mem_Cfix.2 ⟨v₁.2, hv₁, by rw [hψ₁]; exact hw₁⟩))
    (Subgroup.mem_sup_right (mem_Cfix.2 ⟨v₂.2, hv₂, by rw [hψ₂]; exact hw₂⟩))

@[expose] def conjOn (B : Subgroup Γ) (t : Γ) (ht : t ∈ Subgroup.normalizer (B : Set Γ)) :
    ↥B ≃* ↥B where
  toFun x := ⟨t * x * t⁻¹, (Subgroup.mem_normalizer_iff.mp ht x).mp x.2⟩
  invFun x := ⟨t⁻¹ * x * t, by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht) x).mp x.2
    simpa using this⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem symFiveRigid : SymFiveRigid := by
  intro Γ _ _ G T V φ ψ T' S E h z _ hzV hz2 hzG hsq
  classical
  obtain ⟨a, b, c, d, hab, hcd, hac, had, hbc, hbd, hT'⟩ := exists_points S
  have hY : imgG G φ (baum T) = Subgroup.zpowers (swap a b) ⊔ Subgroup.zpowers (swap c d) := by
    rw [S.baum, hT', closure_pair_eq_sup]
  have hp : Pts G T φ a b c d := ⟨hab, hcd, hac, had, hbc, hbd, hY⟩
  have hker : kerG G φ ≤ T := h.ker_le_T
  have hV : V1Iso S ⁅V, E⁆ := h.v1Iso
  have hz2' : z * z = 1 := by rw [← sq]; exact hz2
  set θ : ℕ := (Wset G T φ ⊥).ncard + (Wset G T φ (Subgroup.zpowers (swap a b))).ncard with hθ
  have hθpos : 0 < θ := lt_of_lt_of_le (Wset_bot_pos hV hp) (Nat.le_add_right _ _)
  set B : Subgroup Γ := baum T with hB
  have hBT : B ≤ T := inf_le_left
  have hBG : B ≤ G := hBT.trans S.sylow.1
  set Smu' : Subgroup ↥B := multSub ↥B θ with hSmu'
  set Smu : Subgroup Γ := Smu'.map B.subtype with hSmu
  have hmem : ∀ v : Γ, θ ≤ (memSet T v).ncard → v ∈ Smu := by
    intro v hμ
    have hne : (memSet T v).Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨A, hA, hvA⟩ := hne
    have hvB : v ∈ B := le_baum_of_member hA hvA
    have : (⟨v, hvB⟩ : ↥B) ∈ Smu' :=
      Subgroup.subset_closure (by show θ ≤ multB (⟨v, hvB⟩ : ↥B); rw [multB_eq_ncard hvB]; exact hμ)
    exact ⟨_, this, rfl⟩
  have hV₁S : ⁅V, E⁆ ≤ Smu :=
    (V₁_le_sup_Cfix hV hp).trans (sup_le (fun v hv => hmem v (lower_t₁ hV hp hv))
      (fun v hv => hmem v (lower_t₂ h hker hV hp hv)))
  have hSker : Smu ≤ kerG G φ := by
    rw [hSmu, Subgroup.map_le_iff_le_comap, hSmu', multSub, Subgroup.closure_le]
    intro x' hx'
    have hx'B : (x' : Γ) ∈ B := x'.2
    have hxG : (x' : Γ) ∈ G := hBG hx'B
    show (x' : Γ) ∈ kerG G φ
    refine mem_kerG.2 ⟨hxG, ?_⟩
    by_contra hne
    have hlt := strict_B h hker hV hp hz2' hzG hzV hsq hx'B hxG hne
    have hge : θ ≤ multB x' := hx'
    have heq : multB x' = (memSet T (x' : Γ)).ncard := multB_eq_ncard hx'B
    omega
  have hEN : ∀ e ∈ E, ∀ x ∈ Smu, e * x * e⁻¹ ∈ Smu := by
    intro e he x hx
    have hc1 : ⁅x, e⁆ ∈ ⁅V, E⁆ := h.comm_R_E (hSker hx) he
    have e1 : e * x * e⁻¹ = (⁅x, e⁆)⁻¹ * x := by
      simp only [commutatorElement_def]
      group
    rw [e1]
    exact Smu.mul_mem (Smu.inv_mem (hV₁S hc1)) hx
  have hTN : ∀ t ∈ T, ∀ x ∈ Smu, t * x * t⁻¹ ∈ Smu := by
    intro t ht x hx
    have htB : t ∈ Subgroup.normalizer (B : Set Γ) := le_normalizer_baum T ht
    obtain ⟨x', hx', rfl⟩ := hx
    have hch := Subgroup.characteristic_iff_map_le.1 (multSub_characteristic (H := ↥B) θ)
      (conjOn B t htB)
    exact ⟨conjOn B t htB x', hch ⟨x', hx', rfl⟩, rfl⟩
  have hGN : G ≤ Subgroup.normalizer (Smu : Set Γ) := by
    refine h.sup.trans (sup_le (fun e he => ?_) (fun t ht => ?_))
    · exact B6.mem_normalizer_of_forall_mem (hEN e he) fun x hx => by
        simpa using hEN e⁻¹ (E.inv_mem he) x hx
    · exact B6.mem_normalizer_of_forall_mem (hTN t ht) fun x hx => by
        simpa using hTN t⁻¹ (T.inv_mem ht) x hx
  have hSB : Smu ≤ B := Subgroup.map_subtype_le _
  have hS0 : Smu ≠ ⊥ := by
    intro h0
    have h1 : ⁅V, E⁆ = ⊥ := le_bot_iff.1 (h0 ▸ hV₁S)
    have h2 : Nat.card ↥(⁅V, E⁆ : Subgroup Γ) = 16 := card_V₁ hV
    rw [h1, Subgroup.card_bot] at h2
    omega
  have hchar : (Smu.subgroupOf B).Characteristic := by
    have : Smu.subgroupOf B = Smu' := by
      rw [hSmu, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective B.subtype_injective]
    rw [this]
    exact multSub_characteristic θ
  exact noCharNormal_baum_of_cStarIn_ne S.ne Smu hSB hS0 hchar hGN

theorem symCaseTwoFive : SymCaseTwoFive := symCaseTwoFive_of_rigid symFiveRigid

theorem threeEightSymmIH_proved : ThreeEightSymmIH := threeEightSymmIH_of_five symCaseTwoFive

end CFSG.CGT.PushingUpLit.SYMB
