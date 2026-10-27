module

public import CFSG.CGT.PushingUpLit.SolK.Length
public import CFSG.CGT.PushingUpLit.SolK.Fusion
public import CFSG.CGT.PushingUpLit.SolK.PermBlock

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

theorem theta_eq_one_of_pCore {x : G} {l : ℕ} (hl : S.HasLen x l) (hl2 : l ≠ 2) (hl4 : l ≠ 4)
    {t : G}
    (ht : t ∈ pCoreOf 2 (M ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G))) :
    ∃ htM : t ∈ M, S.θ ⟨t, htM⟩ = 1 := by
  classical
  set C1 : Subgroup G := M ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)
    with hC1
  set T0 : Subgroup G := pCoreOf 2 C1 with hT0
  have hT0C : T0 ≤ C1 := pCoreOf_le_self C1
  have hT0M : T0 ≤ M := hT0C.trans inf_le_left
  have hl' := hl
  obtain ⟨w, hw, r, hr, rfl, hcard⟩ := hl'
  set v : ↥(coreMod (2 * n + 1)) := S.D.β ⟨w, hw⟩ with hv
  set I : Finset (Fin (2 * n + 1)) := vsupp v with hI
  have hcomm : ∀ m : ↥M, (m : G) ∈ C1 → (m : G) * (w * r) * (m : G)⁻¹ = w * r := fun m hm =>
    mem_centralizer_zpowers_iff.1 (Subgroup.mem_inf.1 hm).2
  let K : Subgroup ↥M := T0.subgroupOf M
  have hmemK : ∀ m : ↥M, m ∈ K ↔ (m : G) ∈ T0 := fun m => Iff.rfl
  have hK2 : IsPGroup 2 ↥K :=
    (isPGroup_pCoreOf' C1).of_equiv (Subgroup.subgroupOfEquivOfLe hT0M).symm
  set N : Subgroup (Perm (Fin (2 * n + 1))) := K.map S.θ with hN
  have hN2 : IsPGroup 2 N := hK2.map S.θ
  have hNI : N ≤ setStab I := by
    rintro σ hσ
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hσ
    have hmC : (m : G) ∈ C1 := hT0C ((hmemK m).1 hm)
    exact (coreAct_eq_iff _ _).1 (S.fix_of_comm hw hr m (hcomm m hmC))
  have key : ∀ τ ∈ alternatingGroup (Fin (2 * n + 1)), τ ∈ setStab I →
      ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N := by
    intro τ hτ hτI σ hσ
    obtain ⟨c, hcτ⟩ := S.D.ρ_surj τ hτ
    have hcI : S.D.ρ c = τ := hcτ
    have hfix : coreAct (2 * n + 1) (S.D.ρ c) v = v := by
      rw [hcI]
      exact (coreAct_eq_iff _ _).2 hτI
    have hcx := S.comm_of_fix_X hw hr c hfix
    have hcM : (c : G) ∈ M := S.hyp.le c.2
    have hcC : (c : G) ∈ C1 := Subgroup.mem_inf.2
      ⟨hcM, mem_centralizer_zpowers_iff.2 hcx⟩
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hσ
    have hcmT : (c : G) * (m : G) * (c : G)⁻¹ ∈ T0 :=
      pCoreOf_normalized C1 hcC ((hmemK m).1 hm)
    refine Subgroup.mem_map.2 ⟨⟨(c : G) * (m : G) * (c : G)⁻¹, hT0M hcmT⟩, hcmT, ?_⟩
    have hθc : S.θ ⟨(c : G), hcM⟩ = τ := by rw [S.θ_X c]; exact hcI
    have : (⟨(c : G) * (m : G) * (c : G)⁻¹, hT0M hcmT⟩ : ↥M) =
        ⟨(c : G), hcM⟩ * m * ⟨(c : G), hcM⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, hθc]
  have hA : ∀ τ ∈ altOn I, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N := fun τ hτ =>
    key τ (Equiv.Perm.mem_alternatingGroup.2 (mem_altOn.1 hτ).2) (altOn_le_setStab I hτ)
  have hA' : ∀ τ ∈ altOn Iᶜ, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N := fun τ hτ =>
    key τ (Equiv.Perm.mem_alternatingGroup.2 (mem_altOn.1 hτ).2) (by
      intro y
      have := altOn_le_setStab Iᶜ hτ y
      rw [Finset.mem_compl, Finset.mem_compl] at this
      exact not_iff_not.1 this)
  have hlev : Even l := hl.even
  have hlle : l ≤ 2 * n + 1 := hl.le
  have hIc : I.card = l := hcard
  have hIc' : Iᶜ.card = 2 * n + 1 - l := by
    rw [Finset.card_compl, Fintype.card_fin, hIc]
  obtain ⟨k, hk⟩ := hlev
  have hbot : N = ⊥ := by
    refine eq_bot_of_blocks hN2 hNI hA hA' ?_ ?_
    · rw [hIc]; omega
    · rw [hIc']; omega
  refine ⟨hT0M ht, ?_⟩
  have hmem : S.θ ⟨t, hT0M ht⟩ ∈ N := Subgroup.mem_map.2 ⟨⟨t, hT0M ht⟩, (hmemK _).2 ht, rfl⟩
  rw [hbot] at hmem
  exact Subgroup.mem_bot.1 hmem

theorem pCoreOf_centralizer_le_of_len (hT : TightData S) {x : G} {l : ℕ} (hl : S.HasLen x l)
    (hl2 : l ≠ 2) (hl4 : l ≠ 4) :
    pCoreOf 2 (M ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)) ≤
      pCoreOf 2 M := by
  intro t ht
  obtain ⟨htM, hθ⟩ := S.theta_eq_one_of_pCore hl hl2 hl4 ht
  obtain ⟨j, hj⟩ := isPGroup_pCoreOf' (M ⊓ Subgroup.centralizer
    ((Subgroup.zpowers x : Subgroup G) : Set G)) ⟨t, ht⟩
  exact hT.ker_two ⟨t, htM⟩ hθ ⟨j, by simpa using congrArg Subtype.val hj⟩

theorem centralizer_eq_of_len (hchar : IsCharTwoType G) (hT : TightData S) {x : G}
    (hxQ : x ∈ pCoreOf 2 M) (hx1 : x ≠ 1) {l : ℕ} (hl : S.HasLen x l) (hl2 : l ≠ 2)
    (hl4 : l ≠ 4) :
    pCoreOf 2 (Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)) =
        pCoreOf 2 M ∧
      Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ M :=
  S.centralizer_le_M hchar hT.abelian (Subgroup.zpowers_le.2 hxQ)
    (by simpa [Subgroup.zpowers_eq_bot] using hx1)
    (S.pCoreOf_centralizer_le_of_len hT hl hl2 hl4)

theorem conj_le_of_len (hchar : IsCharTwoType G) (hT : TightData S) {x y g : G}
    (hxQ : x ∈ pCoreOf 2 M) (hx1 : x ≠ 1) (hyQ : y ∈ pCoreOf 2 M) (hy1 : y ≠ 1)
    {l l' : ℕ} (hl : S.HasLen x l) (hl' : S.HasLen y l') (hl2 : l ≠ 2) (hl4 : l ≠ 4)
    (hl2' : l' ≠ 2) (hl4' : l' ≠ 4) (hg : g * x * g⁻¹ = y) :
    ∀ q ∈ pCoreOf 2 M, g * q * g⁻¹ ∈ pCoreOf 2 M := by
  have hX := (S.centralizer_eq_of_len hchar hT hxQ hx1 hl hl2 hl4).1
  have hY := (S.centralizer_eq_of_len hchar hT hyQ hy1 hl' hl2' hl4').1
  set H : Subgroup G := Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) with hH
  set P : Subgroup G := (pCoreOf 2 M).map (MulAut.conj g).toMonoidHom with hP
  have hP2 : IsPGroup 2 P := (isPGroup_pCoreOf' M).map _
  have hQH : ∀ q ∈ pCoreOf 2 M, q ∈ Subgroup.centralizer
      ((Subgroup.zpowers x : Subgroup G) : Set G) := fun q hq =>
    mem_centralizer_zpowers_iff.2 (mul_inv_eq_iff_eq_mul.2 (hT.abelian q hq x hxQ))
  have hPH : P ≤ H := by
    rintro _ ⟨q, hq, rfl⟩
    refine mem_centralizer_zpowers_iff.2 ?_
    have h1 := mem_centralizer_zpowers_iff.1 (hQH q hq)
    show g * q * g⁻¹ * y * (g * q * g⁻¹)⁻¹ = y
    rw [← hg]
    calc g * q * g⁻¹ * (g * x * g⁻¹) * (g * q * g⁻¹)⁻¹ = g * (q * x * q⁻¹) * g⁻¹ := by group
      _ = g * x * g⁻¹ := by rw [h1]
  have hnorm : ∀ k ∈ H, ∀ p ∈ P, k * p * k⁻¹ ∈ P := by
    intro k hk p hp
    obtain ⟨q, hq, rfl⟩ := hp
    have hk' : g⁻¹ * k * g ∈ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
      refine mem_centralizer_zpowers_iff.2 ?_
      have h1 := mem_centralizer_zpowers_iff.1 hk
      rw [← hg] at h1
      calc g⁻¹ * k * g * x * (g⁻¹ * k * g)⁻¹ = g⁻¹ * (k * (g * x * g⁻¹) * k⁻¹) * g := by group
        _ = x := by rw [h1]; group
    have hq' : (g⁻¹ * k * g) * q * (g⁻¹ * k * g)⁻¹ ∈ pCoreOf 2 M := by
      rw [← hX] at hq ⊢
      exact pCoreOf_normalized _ hk' hq
    refine ⟨(g⁻¹ * k * g) * q * (g⁻¹ * k * g)⁻¹, hq', ?_⟩
    show g * ((g⁻¹ * k * g) * q * (g⁻¹ * k * g)⁻¹) * g⁻¹ = k * (g * q * g⁻¹) * k⁻¹
    group
  have hle : P ≤ pCoreOf 2 H := le_pCoreOf_of_normalized hPH hnorm hP2
  rw [hH, hY] at hle
  intro q hq
  exact hle ⟨q, hq, rfl⟩

theorem mem_of_conj_of_len (hchar : IsCharTwoType G) (hT : TightData S) {x y g : G}
    (hxQ : x ∈ pCoreOf 2 M) (hx1 : x ≠ 1) (hyQ : y ∈ pCoreOf 2 M) (hy1 : y ≠ 1)
    {l l' : ℕ} (hl : S.HasLen x l) (hl' : S.HasLen y l') (hl2 : l ≠ 2) (hl4 : l ≠ 4)
    (hl2' : l' ≠ 2) (hl4' : l' ≠ 4) (hg : g * x * g⁻¹ = y) : g ∈ M := by
  have h1 := S.conj_le_of_len hchar hT hxQ hx1 hyQ hy1 hl hl' hl2 hl4 hl2' hl4' hg
  have h2 : g⁻¹ * y * g⁻¹⁻¹ = x := by rw [← hg]; group
  have h3 := S.conj_le_of_len hchar hT hyQ hy1 hxQ hx1 hl' hl hl2' hl4' hl2 hl4 h2
  rw [← S.normalizer_Q_eq, Subgroup.mem_normalizer_iff]
  intro q
  refine ⟨h1 q, fun hq => ?_⟩
  have := h3 _ hq
  simpa [mul_assoc] using this

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
