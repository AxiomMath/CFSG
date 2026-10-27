module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BLocalMod27
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BLocalFus
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BLocalHeis
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BLocalHeisMat

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns CFSG.RankThree.PartTwo.Sec4
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Matrix

theorem l3b_card_le_nine {G : Type*} [Group G] {n : ℕ} [NeZero n]
    (ψ : G →* Multiplicative (ZMod n) × Multiplicative (ZMod n)) (hψ : Function.Injective ψ)
    (h3 : ∀ x : G, x ^ 3 = 1) : Nat.card G ≤ 9 := by
  classical
  let S : Finset (Multiplicative (ZMod n)) := Finset.univ.filter fun a => a ^ 3 = 1
  have hS : S.card ≤ 3 := IsCyclic.card_pow_eq_one_le (α := Multiplicative (ZMod n)) (by norm_num)
  have hmem : ∀ x : G, ψ x ∈ S ×ˢ S := by
    intro x
    have h := congrArg ψ (h3 x)
    rw [map_pow, map_one] at h
    simp only [Finset.mem_product, S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  have : Nat.card G ≤ Nat.card ↥(S ×ˢ S) :=
    Nat.card_le_card_of_injective (fun x => (⟨ψ x, hmem x⟩ : ↥(S ×ˢ S)))
      (fun x y hxy => hψ (congrArg Subtype.val hxy))
  have hc : Nat.card ↥(S ×ˢ S) = S.card * S.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_product]
  rw [hc] at this
  exact this.trans (Nat.mul_le_mul hS hS)

section Heis

variable {π : Bool} {p f : ℕ} {K : Type} [Field K] {X : Type} [Group X]
  {φ : X →* GL (Fin 3) K}

theorem l3b_heis_rel {τ : K} (hτ : τ ^ 3 = 1) (hτ0 : τ ≠ 0) :
    diagTau hτ * cycThree * (diagTau hτ)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) * cycThree := by
  set u : Kˣ := Units.mk0 τ hτ0 with hu
  have hu3 : u ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hτ, Units.val_one])
  have h1 := cycThree_pow_conj_diagTau hτ hτ0 1
  rw [pow_one, mul_one] at h1
  have hsc : ∀ s : Kˣ, ∀ A : GL (Fin 3) K,
      A * GeneralLinearGroup.scalar (Fin 3) s = GeneralLinearGroup.scalar (Fin 3) s * A :=
    fun s A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar s A).eq
  have h2 : cycThree * diagTau hτ =
      GeneralLinearGroup.scalar (Fin 3) (u ^ 2) * diagTau hτ * cycThree := by
    calc cycThree * diagTau hτ = cycThree * diagTau hτ * cycThree⁻¹ * cycThree := by group
      _ = _ := by rw [h1]
  have hinv : GeneralLinearGroup.scalar (Fin 3) u * GeneralLinearGroup.scalar (Fin 3) (u ^ 2) = 1 := by
    rw [← map_mul, ← pow_succ', hu3, map_one]
  have h3 : diagTau hτ * cycThree = GeneralLinearGroup.scalar (Fin 3) u * (cycThree * diagTau hτ) := by
    rw [h2]
    calc diagTau hτ * cycThree = (GeneralLinearGroup.scalar (Fin 3) u *
          GeneralLinearGroup.scalar (Fin 3) (u ^ 2)) * (diagTau hτ * cycThree) := by
          rw [hinv]; group
      _ = GeneralLinearGroup.scalar (Fin 3) u * (GeneralLinearGroup.scalar (Fin 3) (u ^ 2) *
          diagTau hτ * cycThree) := by group
  calc diagTau hτ * cycThree * (diagTau hτ)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) u * (cycThree * diagTau hτ) * (diagTau hτ)⁻¹ := by
        rw [h3]
    _ = GeneralLinearGroup.scalar (Fin 3) u * cycThree := by group


theorem l3b_exists_heis (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hφ : L3Model π p f φ) {τ : K} (hτ : τ ^ 3 = 1) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) :
    ∃ x₁ x₂ : X, φ x₁ = g * diagTau hτ * g⁻¹ ∧ φ x₂ = g * cycThree * g⁻¹ := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨x₁, h₁⟩ := hφ.exists_of_mem_sl (conj_mem_slPi hπ hg (diagTau_mem_slPi hπ hq' hτ))
  obtain ⟨x₂, h₂⟩ := hφ.exists_of_mem_sl (conj_mem_slPi hπ hg (cycThree_mem_slPi hπ))
  exact ⟨x₁, x₂, h₁, h₂⟩

theorem l3b_heis_data [Finite X] (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hφ : L3Model π p f φ)
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K)
    {x₁ x₂ : X} (h₁ : φ x₁ = g * diagTau hτ * g⁻¹) (h₂ : φ x₂ = g * cycThree * g⁻¹)
    {E : Subgroup (X ⧸ Subgroup.center X)}
    (hE : E = Subgroup.zpowers (QuotientGroup.mk x₁ : X ⧸ Subgroup.center X) ⊔
      Subgroup.zpowers (QuotientGroup.mk x₂ : X ⧸ Subgroup.center X)) :
    IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ AutHasQ8 E ∧
      (∀ w : X ⧸ Subgroup.center X, (∀ e ∈ E, e * w = w * e) → w ∈ E) ∧
      (∀ e ∈ E, ∃ x : X, (QuotientGroup.mk x : X ⧸ Subgroup.center X) = e ∧ x ^ 3 = 1) := by
  classical
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have h3 := hK.three_ne_zero hq
  set Zc := Subgroup.center X with hZc
  have hι := l3bIota_injective φ hK hq hφ
  have hsurj := l3bIota_surj φ hK hq hφ
  have h₁' : l3bIota φ hK hq hφ (QuotientGroup.mk x₁) =
      ProjGenLinGroup.mk (g * diagTau hτ * g⁻¹) := by rw [l3bIota_mk, h₁]
  have h₂' : l3bIota φ hK hq hφ (QuotientGroup.mk x₂) =
      ProjGenLinGroup.mk (g * cycThree * g⁻¹) := by rw [l3bIota_mk, h₂]
  obtain ⟨n₁, n₂, h12, h1, h2, hx1, hx2, hF1, hF2, hN1, hN2⟩ :=
    l3b_heis_pair (l3bIota φ hK hq hφ) hι hsurj hK hq hτ hτ1 hg h₁' h₂'
  obtain ⟨hE1, hE2, hE3, -⟩ := l3b_heis_q8_data (J := ⊤) hE h12 h1 h2 hx1 hx2 hF1 hF2 hN1 hN2
    trivial trivial
  have hcard3 : Nat.card Zc = 3 := hφ.card_center hK hq
  have hx₁3 : x₁ ^ 3 = 1 := by
    apply hφ.inj
    rw [map_pow, map_one, h₁, conj_pow, diagTau_pow_three hτ]; group
  have hx₂3 : x₂ ^ 3 = 1 := by
    apply hφ.inj
    rw [map_pow, map_one, h₂, conj_pow, cycThree_pow_three]; group
  refine ⟨hE1, hE2, hE3, ?_, ?_⟩
  ·
    intro w hw
    set C := Subgroup.centralizer (E : Set (X ⧸ Zc)) with hC
    have hEC : E ≤ C := by
      intro e he
      rw [hC, Subgroup.mem_centralizer_iff]
      intro h hh
      exact congrArg Subtype.val (hE1.1.is_comm.comm ⟨h, hh⟩ ⟨e, he⟩)
    have hwC : w ∈ C := by
      rw [hC, Subgroup.mem_centralizer_iff]
      exact fun h hh => hw h hh
    have hX₁E : (QuotientGroup.mk x₁ : X ⧸ Zc) ∈ E := by
      rw [hE]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    have hX₂E : (QuotientGroup.mk x₂ : X ⧸ Zc) ∈ E := by
      rw [hE]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    choose lift hlift using fun w : X ⧸ Zc => QuotientGroup.mk_surjective w
    have hz : ∀ (w : C) (x : X), (QuotientGroup.mk x : X ⧸ Zc) ∈ E →
        x⁻¹ * (lift w * x * (lift w)⁻¹) ∈ Zc := by
      intro w x hx
      rw [← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hlift]
      have := (Subgroup.mem_centralizer_iff.1 w.2) _ hx
      rw [← this]; group
    let F : C → Zc × Zc := fun w => (⟨_, hz w x₁ hX₁E⟩, ⟨_, hz w x₂ hX₂E⟩)
    have hFinj : Function.Injective F := by
      intro w w' hww
      simp only [F, Prod.mk.injEq, Subtype.mk.injEq] at hww
      obtain ⟨e1, e2⟩ := hww
      have c1 : lift w * x₁ * (lift w)⁻¹ = lift w' * x₁ * (lift w')⁻¹ := mul_left_cancel e1
      have c2 : lift w * x₂ * (lift w)⁻¹ = lift w' * x₂ * (lift w')⁻¹ := mul_left_cancel e2
      set r := (lift w)⁻¹ * lift w' with hr
      have rx : ∀ x : X, lift w * x * (lift w)⁻¹ = lift w' * x * (lift w')⁻¹ → r * x = x * r := by
        intro x hx
        calc r * x = (lift w)⁻¹ * (lift w' * x * (lift w')⁻¹) * lift w' := by rw [hr]; group
          _ = (lift w)⁻¹ * (lift w * x * (lift w)⁻¹) * lift w' := by rw [hx]
          _ = x * r := by rw [hr]; group
      have hy : φ x₁ * φ x₂ * (φ x₁)⁻¹ =
          GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) * φ x₂ := by
        rw [h₁, h₂]
        have hs := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar (Units.mk0 τ hτ0) g).eq
        calc g * diagTau hτ * g⁻¹ * (g * cycThree * g⁻¹) * (g * diagTau hτ * g⁻¹)⁻¹ =
            g * (diagTau hτ * cycThree * (diagTau hτ)⁻¹) * g⁻¹ := by group
          _ = g * (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) * cycThree) * g⁻¹ := by
            rw [l3b_heis_rel hτ hτ0]
          _ = (g * GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0)) * cycThree * g⁻¹ := by
            group
          _ = (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) * g) * cycThree * g⁻¹ := by
            rw [hs]
          _ = _ := by group
      have hζ1 : Units.mk0 τ hτ0 ≠ 1 := fun h => hτ1 (by simpa using congrArg Units.val h)
      have hζ3 : (Units.mk0 τ hτ0 : Kˣ) ^ 3 = 1 := Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_mk0, hτ, Units.val_one])
      have hrs := mem_statedScalars_of_commute_heis h3 hζ1 hζ3 hy
        (r := φ r) (by rw [← map_mul, ← map_mul, rx x₁ c1]) (by rw [← map_mul, ← map_mul, rx x₂ c2])
      have hrZ : r ∈ Zc := (hφ.mem_center_iff hK hq r).2 hrs
      have hab : (QuotientGroup.mk (lift w) : X ⧸ Zc) = QuotientGroup.mk (lift w') := by
        have : (QuotientGroup.mk r : X ⧸ Zc) = 1 := (QuotientGroup.eq_one_iff r).2 hrZ
        rw [hr, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at this
        exact inv_mul_eq_one.1 this
      rw [hlift, hlift] at hab
      exact Subtype.ext hab
    have hCle : Nat.card C ≤ 9 := by
      calc Nat.card C ≤ Nat.card (Zc × Zc) := Nat.card_le_card_of_injective F hFinj
        _ = 9 := by rw [Nat.card_prod, hcard3]
    have hEeq : E = C := Subgroup.eq_of_le_of_card_ge hEC (by rw [hE2]; exact hCle)
    rw [hEeq]; exact hwC
  ·
    intro e he
    rw [hE] at he
    obtain ⟨i, j, rfl⟩ := CFSG.RankThree.PartTwo.Sec4.exists_zpow_mul_of_mem_sup h12 he
    refine ⟨x₁ ^ i * x₂ ^ j, by simp [QuotientGroup.mk_mul, QuotientGroup.mk_zpow], ?_⟩
    set a := x₁ ^ i with ha
    set b := x₂ ^ j with hb
    have hab : (QuotientGroup.mk (b * a) : X ⧸ Zc) = QuotientGroup.mk (a * b) := by
      simp only [QuotientGroup.mk_mul, ha, hb, QuotientGroup.mk_zpow]
      exact ((Commute.zpow_zpow (show Commute (QuotientGroup.mk x₂ : X ⧸ Zc)
        (QuotientGroup.mk x₁) from h12.symm) j i).eq)
    set c := (a * b)⁻¹ * (b * a) with hc
    have hcZ : c ∈ Zc := by
      rw [← QuotientGroup.eq_one_iff, hc, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hab,
        inv_mul_cancel]
    have hbac : b * a = a * b * c := by rw [hc]; group
    rw [l3b_cube_mul (fun y => Subgroup.mem_center_iff.1 hcZ y) hbac (hφ.center_pow hK hq hcZ)]
    have ha3 : a ^ 3 = 1 := by
      rw [ha, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hx₁3, _root_.one_zpow]
    have hb3 : b ^ 3 = 1 := by
      rw [hb, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hx₂3, _root_.one_zpow]
    rw [ha3, hb3, one_mul]

end Heis

end CFSG.HardMathSupport.Solomon.Coordinator
