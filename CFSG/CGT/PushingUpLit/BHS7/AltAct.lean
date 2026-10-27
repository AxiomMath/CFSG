module

public import CFSG.CGT.PushingUpLit.BHS7.OmegaSL

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T E : Subgroup Γ}

structure AltAct (G T E : Subgroup Γ) (m : ℕ) where
  Φ : ↥(E ⊔ baum T) →* Equiv.Perm (Fin (2 * m + 1))
  surj : Function.Surjective Φ
  ker_iff : ∀ x : ↥(E ⊔ baum T),
    Φ x = 1 ↔ (x : Γ) ∈ Subgroup.centralizer (pCoreOf 2 E : Set Γ)
  alt_of_mem : ∀ x : ↥(E ⊔ baum T), (x : Γ) ∈ E →
    Φ x ∈ alternatingGroup (Fin (2 * m + 1))
  exists_of_alt : ∀ a ∈ alternatingGroup (Fin (2 * m + 1)),
    ∃ x : ↥(E ⊔ baum T), (x : Γ) ∈ E ∧ Φ x = a
  β : ↥(pCoreOf 2 E) → ↥(coreMod (2 * m + 1))
  β_inj : Function.Injective β
  β_one : β 1 = 1
  β_compat : ∀ (x : ↥(E ⊔ baum T)) (w w' : ↥(pCoreOf 2 E)), (w' : Γ) = (x : Γ) * w * (x : Γ)⁻¹ →
    β w' = coreAct (2 * m + 1) (Φ x) (β w)
  k : ℕ
  one_le_k : 1 ≤ k
  k_le : k ≤ m
  baum_swap : IsSwapGroupOfSize
    (((baum T).subgroupOf (E ⊔ baum T)).map Φ) k
  card_baum : Nat.card ↥(autOn (baum T) (pCoreOf 2 E)) = 2 ^ k

theorem nonempty_altAct (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E) {m : ℕ}
    (hm : 1 ≤ m) (hn : IsNaturalAltModule ↥E m) : Nonempty (AltAct G T E m) := by
  classical
  set W : Subgroup Γ := pCoreOf 2 E with hWdef
  have hWe : IsElemAbelian 2 W :=
    isElemAbelian_of_forall' hE.elemAbelian.1 hE.elemAbelian.2
  let _ : CommGroup ↥W := commGroupOfElemAbelian hWe
  obtain ⟨D, ψ, hψβ, hβbij, hψbij, hsup, hJeq, k, hk1, hk2, hYswap, hcard, -⟩ :=
    block_structure_symm hG hT hE hm hn (W := W) rfl hWe
  have hEW : E ≤ Subgroup.normalizer (W : Set Γ) := le_normalizer_pCoreOf_self E
  have hBW : baum T ≤ Subgroup.normalizer (W : Set Γ) :=
    (baum_le_normalizer_of_isBTBlock hE).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  have hHW : E ⊔ baum T ≤ Subgroup.normalizer (W : Set Γ) := sup_le hEW hBW
  let N : Subgroup (MulAut ↥W) := Subgroup.normalizer (autOn E W : Set (MulAut ↥W))
  have hautE_N : autOn E W ≤ N := Subgroup.le_normalizer
  have hautB_N : autOn (baum T) W ≤ N :=
    (le_sup_right : autOn (baum T) W ≤ autOn E W ⊔ autOn (baum T) W).trans hsup.le
  have hHN : autOn (E ⊔ baum T) W ≤ N :=
    (le_autPre_iff hHW).mp (sup_le ((le_autPre_iff hEW).mpr hautE_N)
      ((le_autPre_iff hBW).mpr hautB_N))
  let act : ↥(E ⊔ baum T) →* ↥N := (actOn W (E ⊔ baum T) hHW).codRestrict N (fun x =>
    hHN (by rw [← range_actOn W _ hHW]; exact ⟨x, rfl⟩))
  have hact : ∀ x, ((act x : ↥N) : MulAut ↥W) = actOn W (E ⊔ baum T) hHW x := fun x => rfl
  have h3 : 3 ≤ 2 * m + 1 := by omega
  have hψθ : ∀ e : ↥(autOn E W),
      ψ ⟨(e : MulAut ↥W), hautE_N e.2⟩ = ((D.θ e : alternatingGroup (Fin (2 * m + 1))) :
        Equiv.Perm (Fin (2 * m + 1))) := fun e =>
    D.perm_unique h3 (fun w => (hψβ ⟨(e : MulAut ↥W), hautE_N e.2⟩ w).symm.trans
      (D.equivar e w))
  have hrange : ∀ y : ↥N, ∃ x : ↥(E ⊔ baum T), act x = y := fun y => by
    have h1 : (y : MulAut ↥W) ∈ autOn (E ⊔ baum T) W := by
      have : (y : MulAut ↥W) ∈ autOn E W ⊔ autOn (baum T) W := by rw [hsup]; exact y.2
      exact sup_le (autOn_le_autOn W le_sup_left) (autOn_le_autOn W le_sup_right) this
    rw [← range_actOn W _ hHW] at h1
    obtain ⟨x, hx⟩ := h1
    exact ⟨x, Subtype.ext hx⟩
  have hsurj : Function.Surjective (ψ.comp act) := fun p => by
    obtain ⟨y, rfl⟩ := hψbij.2 p
    obtain ⟨x, hx⟩ := hrange y
    exact ⟨x, by simp [hx]⟩
  have hker : ∀ x : ↥(E ⊔ baum T),
      (ψ.comp act) x = 1 ↔ (x : Γ) ∈ Subgroup.centralizer (W : Set Γ) := by
    intro x
    show ψ (act x) = 1 ↔ _
    rw [← map_one ψ, hψbij.1.eq_iff]
    constructor
    · intro h
      have h1 : x ∈ (actOn W (E ⊔ baum T) hHW).ker := congrArg Subtype.val h
      rw [ker_actOn, Subgroup.mem_subgroupOf] at h1
      exact h1.2
    · intro hx
      apply Subtype.ext
      show actOn W (E ⊔ baum T) hHW x = 1
      have h1 : x ∈ (actOn W (E ⊔ baum T) hHW).ker := by
        rw [ker_actOn, Subgroup.mem_subgroupOf]
        exact ⟨x.2, hx⟩
      exact h1
  have halt : ∀ x : ↥(E ⊔ baum T), (x : Γ) ∈ E →
      (ψ.comp act) x ∈ alternatingGroup (Fin (2 * m + 1)) := by
    intro x hx
    have hxe : (act x : MulAut ↥W) ∈ autOn E W := by
      rw [hact]
      exact mem_autOn_iff.mpr ⟨⟨x, hHW x.2⟩, hx, rfl⟩
    have h1 := hψθ ⟨(act x : MulAut ↥W), hxe⟩
    have e1 : act x = ⟨(act x : MulAut ↥W), hautE_N hxe⟩ := rfl
    show ψ (act x) ∈ _
    rw [e1, h1]
    exact (D.θ _).2
  have hex : ∀ a ∈ alternatingGroup (Fin (2 * m + 1)),
      ∃ x : ↥(E ⊔ baum T), (x : Γ) ∈ E ∧ (ψ.comp act) x = a := by
    intro a ha
    obtain ⟨e', he'⟩ := D.θ.surjective ⟨a, ha⟩
    obtain ⟨x₀, hx₀E, hx₀⟩ := mem_autOn_iff.mp e'.2
    refine ⟨⟨(x₀ : Γ), (le_sup_left : E ≤ E ⊔ baum T) hx₀E⟩, hx₀E, ?_⟩
    have e1 : act ⟨(x₀ : Γ), (le_sup_left : E ≤ E ⊔ baum T) hx₀E⟩ =
        ⟨(e' : MulAut ↥W), hautE_N e'.2⟩ := Subtype.ext hx₀
    show ψ (act _) = a
    rw [e1, hψθ e', he']
  refine ⟨{
    Φ := ψ.comp act
    surj := hsurj
    ker_iff := hker
    alt_of_mem := halt
    exists_of_alt := hex
    β := (fun w => D.β w)
    β_inj := hβbij.1
    β_one := D.β.map_one
    β_compat := ?_
    k := k
    one_le_k := hk1
    k_le := by omega
    baum_swap := ?_
    card_baum := hcard }⟩
  · intro x w w' hw'
    have h1 : (act x : MulAut ↥W) w = w' :=
      Subtype.ext (by rw [hact, actOn_apply_coe hHW x w]; exact hw'.symm)
    have h2 := hψβ (act x) w
    rw [h1] at h2
    exact h2
  · have heq : ((baum T).subgroupOf (E ⊔ baum T)).map (ψ.comp act) =
        ((autOn (baum T) W).subgroupOf N).map ψ := by
      ext p
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨act x, ?_, rfl⟩
        have hxB : (x : Γ) ∈ baum T := hx
        show (act x : MulAut ↥W) ∈ autOn (baum T) W
        rw [hact]
        exact mem_autOn_iff.mpr ⟨⟨x, hHW x.2⟩, hxB, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        have hyB : (y : MulAut ↥W) ∈ autOn (baum T) W := hy
        obtain ⟨a, ha, hay⟩ := mem_autOn_iff.mp hyB
        refine ⟨⟨(a : Γ), (le_sup_right : baum T ≤ E ⊔ baum T) ha⟩, ha, ?_⟩
        have e1 : act ⟨(a : Γ), (le_sup_right : baum T ≤ E ⊔ baum T) ha⟩ = y := Subtype.ext hay
        show ψ (act _) = ψ y
        rw [e1]
    rw [heq]
    exact hYswap

theorem relIndex_sup_eq_relIndex_inf' {N B : Subgroup Γ}
    (hB : B ≤ Subgroup.normalizer (N : Set Γ)) : B.relIndex (N ⊔ B) = (N ⊓ B).relIndex N := by
  have h1 : (B ⊓ N).relIndex B * B.relIndex (N ⊔ B) = (B ⊓ N).relIndex (N ⊔ B) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left le_sup_right
  have h2 : (B ⊓ N).relIndex N * N.relIndex (N ⊔ B) = (B ⊓ N).relIndex (N ⊔ B) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_left
  have h3 : N.relIndex (N ⊔ B) = (B ⊓ N).relIndex B := by
    rw [sup_comm, A4.relIndex_sup_eq_of_le_normalizer' hB]
    exact (Subgroup.inf_relIndex_left B N).symm
  have h4 : 0 < (B ⊓ N).relIndex B :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := ((B ⊓ N).subgroupOf B)))
  have h5 : B.relIndex (N ⊔ B) = (B ⊓ N).relIndex N :=
    Nat.eq_of_mul_eq_mul_left h4 (by rw [h1, ← h2, h3, mul_comm])
  rw [h5, inf_comm]

theorem isSylowTwoOf_inf_sup_baum (hT : IsPGroup 2 T)
    (hBE : baum T ≤ Subgroup.normalizer (E : Set Γ)) (hS : IsSylowTwoOf (T ⊓ E) E) :
    IsSylowTwoOf (T ⊓ (E ⊔ baum T)) (E ⊔ baum T) := by
  have hBT : baum T ≤ T := inf_le_left
  set Q : Subgroup Γ := T ⊓ (E ⊔ baum T) with hQ
  have hBQ : baum T ≤ Q := le_inf hBT le_sup_right
  have hQH : Q ≤ E ⊔ baum T := inf_le_right
  have hHN : E ⊔ baum T ≤ Subgroup.normalizer (E : Set Γ) :=
    sup_le Subgroup.le_normalizer hBE
  have hQN : Q ≤ Subgroup.normalizer (E : Set Γ) := hQH.trans hHN
  have hEQ : E ⊔ Q = E ⊔ baum T := le_antisymm (sup_le le_sup_left hQH) (sup_le_sup_left hBQ E)
  have hEQ' : E ⊓ Q = T ⊓ E := by
    ext x
    simp only [Subgroup.mem_inf, hQ]
    constructor
    · rintro ⟨hxE, hxT, -⟩
      exact ⟨hxT, hxE⟩
    · rintro ⟨hxT, hxE⟩
      exact ⟨hxE, hxT, (le_sup_left : E ≤ E ⊔ baum T) hxE⟩
  refine ⟨hQH, hT.to_le inf_le_left, ?_⟩
  have h1 : Q.relIndex (E ⊔ Q) = (E ⊓ Q).relIndex E := relIndex_sup_eq_relIndex_inf' hQN
  rw [hEQ, hEQ'] at h1
  intro hd
  have hd' : 2 ∣ Q.relIndex (E ⊔ baum T) := hd
  rw [h1] at hd'
  exact hS.2.2 hd'

theorem inf_centralizer_le_of_isSylowTwoOf (hG : CharTwo G) (hT : IsSylowOf 2 T G)
    (hE : IsBTBlock G T E) (hSH : IsSylowTwoOf (T ⊓ (E ⊔ baum T)) (E ⊔ baum T)) :
    (E ⊔ baum T) ⊓ Subgroup.centralizer (pCoreOf 2 E : Set Γ) ≤ T := by
  have hT2 : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf hT
  have hchar : CharTwo E := charTwo_of_isBTBlock hG hT hE
  have hBE : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hE
  have hB2 : IsPGroup 2 ↥(baum T) := hT2.2.1.to_le inf_le_left
  have hEW : E ≤ Subgroup.normalizer (pCoreOf 2 E : Set Γ) := le_normalizer_pCoreOf_self E
  have hBW : baum T ≤ Subgroup.normalizer (pCoreOf 2 E : Set Γ) :=
    hBE.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  have hHW : E ⊔ baum T ≤ Subgroup.normalizer (pCoreOf 2 E : Set Γ) := sup_le hEW hBW
  set C : Subgroup Γ := (E ⊔ baum T) ⊓ Subgroup.centralizer (pCoreOf 2 E : Set Γ) with hC
  have hCp : IsPGroup 2 C := fun x => by
    obtain ⟨k, hk⟩ := exists_pow_two_eq_one_of_centralizes hchar hE.elemAbelian.1 hB2 hBE
      (x.2.1 : (x : Γ) ∈ E ⊔ baum T) (x.2.2)
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hnorm : E ⊔ baum T ≤ Subgroup.normalizer (C : Set Γ) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ E ⊔ baum T, ∀ x ∈ C, g * x * g⁻¹ ∈ C := by
      intro g hg x hx
      refine Subgroup.mem_inf.mpr ⟨(E ⊔ baum T).mul_mem ((E ⊔ baum T).mul_mem hg
        (Subgroup.mem_inf.mp hx).1) ((E ⊔ baum T).inv_mem hg), ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
      have hw' : g⁻¹ * w * g ∈ pCoreOf 2 E := by
        have := (Subgroup.mem_normalizer_iff.mp (hHW ((E ⊔ baum T).inv_mem hg)) w).mp hw
        simpa using this
      have hc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 _ hw'
      calc w * (g * x * g⁻¹) = g * ((g⁻¹ * w * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * w * g)) * g⁻¹ := by rw [hc]
        _ = (g * x * g⁻¹) * w := by group
    intro x
    exact ⟨fun hx => key h hh x hx, fun hx => by
      have := key h⁻¹ ((E ⊔ baum T).inv_mem hh) _ hx
      simpa [mul_assoc] using this⟩
  exact (hSH.le_of_normalizes inf_le_left hnorm hCp).trans inf_le_left

end CFSG.CGT.PushingUpLit.BHS7
