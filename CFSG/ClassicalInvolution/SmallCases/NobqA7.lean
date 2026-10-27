module

public import CFSG.ClassicalInvolution.SmallCases.NobqOut
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.ClassicalInvolution.Nobq

theorem exists_injective_perm_seven {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    (e : N ≃* alternatingGroup (Fin 7)) (hC : Subgroup.centralizer (N : Set G) = ⊥) :
    ∃ θ : G →* Equiv.Perm (Fin 7), Function.Injective θ := by
  let c : Equiv.Perm (Fin 7) →* MulAut (alternatingGroup (Fin 7)) :=
    MulAut.conjNormal (H := alternatingGroup (Fin 7))
  have hc : Function.Bijective c :=
    CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num)
  let eAut : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) := MulEquiv.ofBijective c hc
  let ψ : G →* MulAut N := MulAut.conjNormal
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have : g ∈ Subgroup.centralizer (N : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have h1 := congrArg (fun φ : MulAut N => ((φ ⟨n, hn⟩ : N) : G)) hg
      have h2 : g * n * g⁻¹ = n := by simpa [ψ] using h1
      calc n * g = (g * n * g⁻¹) * g := by rw [h2]
        _ = g * n := by group
    rw [hC] at this
    exact this
  exact ⟨eAut.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp ψ),
    eAut.symm.injective.comp ((MulAut.congr e).injective.comp hψ)⟩

theorem noDatum_alternating_seven : NoDatum (alternatingGroup (Fin 7)) := by
  intro G _ _ N _ ⟨e⟩ hC R S r hr ⟨eS⟩ t ht ht2 hRC hRn
  obtain ⟨θ, hθ⟩ := exists_injective_perm_seven N e hC
  have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  set S' : Subgroup G := (S : Subgroup R).map R.subtype with hS'
  have hS'R : ∀ x ∈ S', x ∈ R := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hp : IsPGroup 2 S' := S.isPGroup'.map R.subtype
  have hinv : ∀ u ∈ S', orderOf u = 2 → u = t := fun u hu ho =>
    eq_of_orderOf_eq_two_of_datum S eS ht ht2 hRC (hS'R u hu) ho
  have ht1 : θ t ≠ 1 := fun h1 => by
    have : t = 1 := hθ (by rw [h1, map_one])
    rw [this, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  obtain ⟨ω, hω⟩ : ∃ ω : Fin 7, θ t ω ≠ ω := by
    by_contra hcon
    push Not at hcon
    exact ht1 (Equiv.ext hcon)
  have hstab : ∀ s ∈ S', θ s ω = ω → s = 1 := by
    intro s hs hsω
    by_contra hs1
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hp ⟨s, hs⟩
    have hk' : orderOf s = 2 ^ k := (Subgroup.orderOf_coe (⟨s, hs⟩ : S')).trans hk
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hs1 (orderOf_eq_one_iff.mp (by simpa using hk'))
    have hdvd : 2 ^ (k - 1) ∣ orderOf s := by
      rw [hk']
      exact pow_dvd_pow 2 (by omega)
    have h2 : orderOf (s ^ (2 ^ (k - 1))) = 2 := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) hdvd, hk',
        Nat.pow_div (by omega) (by norm_num)]
      have : k - (k - 1) = 1 := by omega
      simp [this]
    have h3 : s ^ (2 ^ (k - 1)) = t := hinv _ (S'.pow_mem hs _) h2
    have h4 : θ (s ^ (2 ^ (k - 1))) ω = ω := by
      rw [map_pow]
      exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hsω _
    rw [h3] at h4
    exact hω h4
  have hinj : Function.Injective (fun s : S' => θ s ω) := by
    intro s s' h
    have h' : θ (s : G) ω = θ (s' : G) ω := h
    have h1 : θ ((s : G)⁻¹ * s') ω = ω := by
      rw [map_mul, map_inv, Equiv.Perm.mul_apply, ← h']
      simp
    have h2 := hstab ((s : G)⁻¹ * (s' : G)) (S'.mul_mem (S'.inv_mem s.2) s'.2) h1
    exact Subtype.ext (inv_mul_eq_one.mp h2)
  have hle : Nat.card S' ≤ 7 := by
    calc Nat.card S' ≤ Nat.card (Fin 7) := Nat.card_le_card_of_injective _ hinj
      _ = 7 := by simp
  have hcard : Nat.card S' = 2 ^ r := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype
      R.subtype_injective).symm.toEquiv, Nat.card_congr eS.toEquiv, Nat.card_eq_fintype_card,
      QuaternionGroup.card]
    have : r = (r - 2) + 2 := by omega
    rw [this, pow_add]
    norm_num [pow_succ]
    ring_nf
  have h8 : 8 ≤ 2 ^ r := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  omega

end CFSG.ClassicalInvolution.Nobq
