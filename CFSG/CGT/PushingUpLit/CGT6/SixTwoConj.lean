module

public import CFSG.CGT.PushingUpLit.CGT6.SixTwoNat
public import CFSG.CGT.PushingUpLit.CGT6.SixTwoSwap
public import CFSG.CGT.PushingUpLit.CGT6.SixTwoJ
public import CFSG.CGT.PushingUpLit.CGT6.SixTwoType

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.Quasithin CFSG.Quasithin.G6
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem card_le_relIndex_mul_card_of_isOffG {V A W : Subgroup G}
    (hV : CFSG.Open.IsElemAbelian 2 V) (hA : IsOffG V A) (hWV : W ≤ V) :
    Nat.card ↥W ≤ (A ⊓ Subgroup.centralizer (W : Set G)).relIndex A *
      Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) := by
  classical
  set A₀ : Subgroup G := A ⊓ Subgroup.centralizer (W : Set G) with hA₀
  set D : Subgroup G := A ⊓ Subgroup.centralizer (V : Set G) with hD
  have hA₀A : A₀ ≤ A := inf_le_left
  have hCVW : Subgroup.centralizer (V : Set G) ≤ Subgroup.centralizer (W : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hWV)
  have hDA₀ : D ≤ A₀ := fun x hx => Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1,
    hCVW (Subgroup.mem_inf.mp hx).2⟩
  have hA₀D : A₀ ⊓ Subgroup.centralizer (V : Set G) = D := by
    ext x
    simp only [Subgroup.mem_inf, hA₀, hD]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hCVW h.2⟩, h.2⟩⟩
  have hw := hA.2.2.2.2 A₀ hA₀A
  unfold wtG at hw
  rw [hA₀D] at hw
  have hrel := Subgroup.relIndex_mul_relIndex D A₀ A hDA₀ hA₀A
  have hr1pos : 0 < D.relIndex A₀ :=
    Nat.pos_of_ne_zero (by unfold Subgroup.relIndex; exact Subgroup.index_ne_zero_of_finite)
  rw [← hrel] at hw
  have h1 : Nat.card ↥(V ⊓ Subgroup.centralizer (A₀ : Set G)) ≤
      A₀.relIndex A * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
    have : D.relIndex A₀ * Nat.card ↥(V ⊓ Subgroup.centralizer (A₀ : Set G)) ≤
        D.relIndex A₀ * (A₀.relIndex A * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))) := by
      calc _ ≤ _ := hw
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left this hr1pos
  set Q : Subgroup G := V ⊓ Subgroup.centralizer (A : Set G) with hQ
  have hWQ : ∀ x ∈ W, ∀ y ∈ Q, x * y = y * x := fun x hx y hy =>
    isElemAbelian_comm' hV (hWV hx) (Subgroup.mem_inf.mp hy).1
  have hprod := card_sup_mul_card_inf' hWQ
  have hsup : Nat.card ↥(W ⊔ Q) ≤ Nat.card ↥(V ⊓ Subgroup.centralizer (A₀ : Set G)) := by
    refine Subgroup.card_le_of_le (sup_le ?_ ?_)
    · intro x hx
      refine Subgroup.mem_inf.mpr ⟨hWV hx, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
      have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hh).2 x hx
      exact this.symm
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1,
        Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hA₀A) (Subgroup.mem_inf.mp hx).2⟩
  have hinf : W ⊓ Q = W ⊓ Subgroup.centralizer (A : Set G) := by
    rw [hQ, ← inf_assoc, inf_eq_left.mpr hWV]
  have hQpos : 0 < Nat.card ↥Q := Nat.card_pos
  have key : Nat.card ↥W * Nat.card ↥Q ≤
      (A₀.relIndex A * Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G))) * Nat.card ↥Q := by
    rw [← hprod]
    calc Nat.card ↥(W ⊔ Q) * Nat.card ↥(W ⊓ Q)
        ≤ (A₀.relIndex A * Nat.card ↥Q) * Nat.card ↥(W ⊓ Q) :=
          Nat.mul_le_mul_right _ (hsup.trans h1)
      _ = (A₀.relIndex A * Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G))) *
          Nat.card ↥Q := by rw [hinf]; ring
  exact Nat.le_of_mul_le_mul_right key hQpos

theorem swap_commutator_pow_ne_one {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (m : ℕ) :
    (Equiv.swap i j * (Equiv.swap i j * Equiv.swap j k) * (Equiv.swap i j)⁻¹ *
      (Equiv.swap i j * Equiv.swap j k)⁻¹) ^ 2 ^ m ≠ 1 := by
  have e : Equiv.swap i j * (Equiv.swap i j * Equiv.swap j k) * (Equiv.swap i j)⁻¹ *
      (Equiv.swap i j * Equiv.swap j k)⁻¹ = (Equiv.swap j k * Equiv.swap i j) ^ 2 := by
    rw [mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv, pow_two]
    calc _ = (Equiv.swap i j * Equiv.swap i j) * Equiv.swap j k * Equiv.swap i j *
          Equiv.swap j k * Equiv.swap i j := by simp only [mul_assoc]
      _ = _ := by rw [Equiv.swap_mul_self, one_mul]; simp only [mul_assoc]
  have hd : (Equiv.swap j k * Equiv.swap i j).IsThreeCycle := by
    rw [Equiv.swap_comm i j]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same hjk (Ne.symm hij) (Ne.symm hik)
  intro h
  rw [e, ← pow_mul] at h
  have h1 := orderOf_dvd_of_pow_eq_one h
  rw [hd.orderOf] at h1
  have h2 : 3 ∣ 2 ^ (1 + m) := by
    have : 2 * 2 ^ m = 2 ^ (1 + m) := by ring
    rwa [this] at h1
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
  omega

theorem mem_altStabilizer {m : ℕ} {F : Finset (Fin m)} {σ : alternatingGroup (Fin m)} :
    σ ∈ altStabilizer m F ↔ ∀ i ∈ F, (σ : Equiv.Perm (Fin m)) i = i := by
  simp only [altStabilizer, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]
  rfl


theorem mem_of_mem_setStab_compl {n : ℕ} {F : Finset (Fin n)} {τ : Equiv.Perm (Fin n)}
    (hτ : τ ∈ setStab Fᶜ) {ℓ : Fin n} (hℓ : ℓ ∈ F) : τ ℓ ∈ F := by
  have h := mem_setStab.mp hτ ℓ
  have h1 : ℓ ∉ Fᶜ := by simpa using hℓ
  have h2 : τ ℓ ∉ Fᶜ := fun hh => h1 (h.mp hh)
  simpa using h2

theorem offConj_of_arrowNat {V Y X : Subgroup G} [V.Normal] (hV : CFSG.Open.IsElemAbelian 2 V)
    (h : PerfCtx V Y X) (hX : InClassX ↥X) (hY : InClassX ↥Y) (hUX : ⁅oTwoIn X, X⁆ ≤ V)
    (harr : ArrowNat Y X) : OffConj V Y X := by
  classical
  rcases harr with rfl | ⟨a, b, φ, F, hYb, hnat, hF, hUU, hYX, himg⟩
  · exact OffConj.of_eq
  intro A hA hAN hnot
  have hb : 1 ≤ b := by
    by_contra hb0
    obtain ⟨e⟩ := hYb
    have hb0' : b = 0 := by omega
    subst hb0'
    have hsub : Subsingleton (alternatingGroup (Fin (2 * 0 + 1))) :=
      ⟨fun x y => Subtype.ext (Equiv.ext fun i => Fin.ext (by
        have h1 := ((x : Equiv.Perm (Fin (2 * 0 + 1))) i).2
        have h2 := ((y : Equiv.Perm (Fin (2 * 0 + 1))) i).2
        omega))⟩
    have hsub' : Subsingleton (↥Y ⧸ pCore 2 ↥Y) := e.injective.subsingleton
    apply InClassX.not_isPGroup hY
    intro y
    have hy : y ∈ pCore 2 ↥Y := (QuotientGroup.eq_one_iff y).mp (Subsingleton.elim _ _)
    obtain ⟨k, hk⟩ := pCore_isPGroup (⟨y, hy⟩ : ↥(pCore 2 ↥Y))
    exact ⟨k, congrArg Subtype.val hk⟩
  have ha : 2 ≤ a := by
    by_contra ha2
    have ha' : a = 0 ∨ a = 1 := by omega
    have hcomm : ∀ σ τ : alternatingGroup (Fin (2 * a + 1)), σ * τ = τ * σ := by
      rcases ha' with rfl | rfl <;> decide
    apply inClassX_not_le_oTwoIn hX
    calc X = ⁅X, X⁆ := h.hperf.symm
      _ ≤ oTwoIn X := by
        refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
        have h1 : toAlt φ ⁅(⟨x, hx⟩ : ↥X), ⟨y, hy⟩⁆ = 1 := by
          rw [map_commutatorElement]
          exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm _ _)
        exact ⟨_, (toAlt_eq_one_iff φ _).mp h1, rfl⟩
  have h3 : 3 ≤ 2 * a + 1 := by omega
  have h5 : 5 ≤ 2 * a + 1 := by omega
  have hodd : Odd (2 * a + 1) := ⟨a, rfl⟩
  have hUV : blockU X ≤ V := hUX
  have hU2 : CFSG.Open.IsElemAbelian 2 (blockU X) := isElemAbelian_mono' hV hUV
  have hXU : X ≤ Subgroup.normalizer (blockU X : Set G) := le_normalizer_blockU X
  have hAU : A ≤ Subgroup.normalizer (blockU X : Set G) := fun g hg =>
    normalizer_le_normalizer_blockU X (hAN hg)
  have hC : X ⊓ Subgroup.centralizer (blockU X : Set G) = oTwoIn X :=
    inf_centralizer_blockU_eq hX.1 h3 hnat
  obtain ⟨D, hD⟩ := exists_altNatData hX.1 h.hperf h3 hnat hU2
  let _ : CommGroup ↥(blockU X) := commGroupOfElemAbelian hU2
  have hW : ∀ w : ↥(blockU X), w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hU2.2 w w.2)
  have hAnorm : (autOn A (blockU X)) ≤
      Subgroup.normalizer ((autOn X (blockU X)) : Set (MulAut ↥(blockU X))) := by
    have key : ∀ g ∈ (autOn A (blockU X)), ∀ e ∈ (autOn X (blockU X)),
        g * e * g⁻¹ ∈ (autOn X (blockU X)) := by
      intro g hg e he
      obtain ⟨a₁, ha₁, rfl⟩ := mem_autOn_iff.mp hg
      obtain ⟨x₁, hx₁, rfl⟩ := mem_autOn_iff.mp he
      refine mem_autOn_iff.mpr ⟨a₁ * x₁ * a₁⁻¹, ?_, ?_⟩
      · have : (a₁ : G) * (x₁ : G) * (a₁ : G)⁻¹ ∈ X :=
          (Subgroup.mem_normalizer_iff.mp (hAN ha₁) _).mp hx₁
        simpa using this
      · rw [map_mul, map_mul, map_inv]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro e
    refine ⟨fun he => key g hg e he, fun hge => ?_⟩
    have := key g⁻¹ ((autOn A (blockU X)).inv_mem hg) _ hge
    simpa [mul_assoc] using this
  have hCUV : Subgroup.centralizer (V : Set G) ≤ Subgroup.centralizer ((blockU X) : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hUV)
  have hAel : @IsElemAbelian2 ↥(blockU X) (commGroupOfElemAbelian hU2) (autOn A (blockU X)) := by
    refine ⟨fun g hg g' hg' => ?_, fun g hg => ?_⟩
    · obtain ⟨a₁, ha₁, rfl⟩ := mem_autOn_iff.mp hg
      obtain ⟨a₂, ha₂, rfl⟩ := mem_autOn_iff.mp hg'
      exact (conjAct_comm_eq_one_iff (blockU X) a₁ a₂).mpr (hCUV (hA.2.2.1 _ ha₁ _ ha₂))
    · obtain ⟨a₁, ha₁, rfl⟩ := mem_autOn_iff.mp hg
      rw [← map_pow, conjAct_eq_one_iff]
      exact hCUV (hA.2.2.2.1 _ ha₁)
  have hAw : Nat.card ↥(blockU X) ≤ Nat.card ↥(autOn A (blockU X)) *
      Nat.card ↥(@fixV ↥(blockU X) (commGroupOfElemAbelian hU2) (autOn A (blockU X))) := by
    rw [card_autOn_eq_relIndex hAU, card_fixV_autOn_eq hU2 hAU]
    exact card_le_relIndex_mul_card_of_isOffG hV hA hUV
  have hEA : ⁅(autOn X (blockU X)), (autOn A (blockU X))⁆ ≠ ⊥ := by
    intro hbot
    apply hnot
    rw [← hC]
    refine Subgroup.commutator_le.mpr fun a ha x hx => ?_
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAN ha) x).mp hx) (X.inv_mem hx)
    · have h1 : conjAct (blockU X) ⟨a, hAU ha⟩ ∈ (autOn A (blockU X)) :=
        mem_autOn_iff.mpr ⟨⟨a, hAU ha⟩, ha, rfl⟩
      have h2 : conjAct (blockU X) ⟨x, hXU hx⟩ ∈ (autOn X (blockU X)) :=
        mem_autOn_iff.mpr ⟨⟨x, hXU hx⟩, hx, rfl⟩
      have h3' := Subgroup.commutator_mem_commutator h2 h1
      rw [hbot, Subgroup.mem_bot, ← map_commutatorElement] at h3'
      have h4 := (conjAct_eq_one_iff (blockU X) _).mp h3'
      have h5 : ⁅a, x⁆ = ⁅x, a⁆⁻¹ := (commutatorElement_inv x a).symm
      rw [h5]
      exact (Subgroup.centralizer ((blockU X) : Set G)).inv_mem h4
  obtain ⟨-, θX, hθXE, hequi, ⟨T, hTne, hTsw, hTc, hTeq⟩, -, -⟩ :=
    alt_core hW hodd h5 D hAnorm hAel hAw hEA
  obtain ⟨t₀, ht₀⟩ := hTne
  have hΩ : 3 ≤ (Fᶜ).card := by
    rw [Finset.card_compl, Fintype.card_fin, hF]
    omega
  obtain ⟨σ, hσalt, hσstab, i, j, hij, hi, hj, hσt₀⟩ :=
    exists_even_conj_swap hodd hTsw hTc ht₀ Fᶜ (by omega)
  obtain ⟨k, hkΩ, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({i, j} : Finset (Fin (2 * a + 1)))) (t := Fᶜ)
    (lt_of_le_of_lt Finset.card_le_two (by omega))
  have hki : k ≠ i := fun e => hk (by simp [e])
  have hkj : k ≠ j := fun e => hk (by simp [e])
  obtain ⟨q, hq⟩ := φ.surjective ⟨σ, hσalt⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hxσ : ((toAlt φ x : alternatingGroup (Fin (2 * a + 1))) : Equiv.Perm (Fin (2 * a + 1))) =
      σ := congrArg Subtype.val hq
  let Nk : Subgroup ↥(Subgroup.normalizer (blockU X : Set G)) :=
    (autOn X (blockU X) ⊔ autOn A (blockU X)).comap (conjAct (blockU X))
  let Θ : ↥Nk →* Equiv.Perm (Fin (2 * a + 1)) :=
    θX.toMonoidHom.comp (((conjAct (blockU X)).comp Nk.subtype).codRestrict
      (autOn X (blockU X) ⊔ autOn A (blockU X)) (fun g => g.2))
  let ιX : ↥X → ↥Nk := fun w => ⟨⟨(w : G), hXU w.2⟩, Subgroup.mem_sup_left
    (mem_autOn_iff.mpr ⟨⟨(w : G), hXU w.2⟩, w.2, rfl⟩)⟩
  let ιA : ↥A → ↥Nk := fun w => ⟨⟨(w : G), hAU w.2⟩, Subgroup.mem_sup_right
    (mem_autOn_iff.mpr ⟨⟨(w : G), hAU w.2⟩, w.2, rfl⟩)⟩
  have hιX : ∀ w : ↥X, ((((ιX w : ↥Nk)) : ↥(Subgroup.normalizer (blockU X : Set G))) : G) =
      (w : G) := fun w => rfl
  have hιA : ∀ w : ↥A, ((((ιA w : ↥Nk)) : ↥(Subgroup.normalizer (blockU X : Set G))) : G) =
      (w : G) := fun w => rfl
  have F1 : ∀ w : ↥X, Θ (ιX w) =
      ((toAlt φ w : alternatingGroup (Fin (2 * a + 1))) : Equiv.Perm (Fin (2 * a + 1))) := by
    intro w
    have h1 := hθXE (actOnRange (blockU X) X hXU w)
    have h2 := congrArg (fun z : alternatingGroup (Fin (2 * a + 1)) =>
      (z : Equiv.Perm (Fin (2 * a + 1)))) (hD w)
    exact h1.trans h2
  have F2 : ∀ w : ↥A, Θ (ιA w) ∈ Subgroup.closure T := by
    intro w
    rw [← hTeq]
    exact ⟨⟨conjAct (blockU X) ⟨(w : G), hAU w.2⟩, Subgroup.mem_sup_right
      (mem_autOn_iff.mpr ⟨⟨(w : G), hAU w.2⟩, w.2, rfl⟩)⟩,
      Subgroup.mem_subgroupOf.mpr (mem_autOn_iff.mpr ⟨⟨(w : G), hAU w.2⟩, w.2, rfl⟩), rfl⟩
  have F3 : ∃ w₀ : ↥A, Θ (ιA w₀) = t₀ := by
    have ht₀' : t₀ ∈ Subgroup.closure T := Subgroup.subset_closure ht₀
    rw [← hTeq] at ht₀'
    obtain ⟨u, hu, hut⟩ := ht₀'
    obtain ⟨g, hg, hgu⟩ := mem_autOn_iff.mp (Subgroup.mem_subgroupOf.mp hu)
    refine ⟨⟨(g : G), hg⟩, ?_⟩
    have hu' : (⟨conjAct (blockU X) g, Subgroup.mem_sup_right
        (mem_autOn_iff.mpr ⟨g, hg, rfl⟩)⟩ : ↥(autOn X (blockU X) ⊔ autOn A (blockU X))) = u :=
      Subtype.ext hgu
    rw [← hut, ← hu']
    rfl
  have F4 : ∀ (w : ↥A) (z y : ↥X),
      (z : G) = (x : G) * (w : G) * (x : G)⁻¹ * (y : G) * ((x : G) * (w : G) * (x : G)⁻¹)⁻¹ →
      ((toAlt φ z : alternatingGroup (Fin (2 * a + 1))) : Equiv.Perm (Fin (2 * a + 1))) =
        (σ * Θ (ιA w) * σ⁻¹) *
          ((toAlt φ y : alternatingGroup (Fin (2 * a + 1))) : Equiv.Perm (Fin (2 * a + 1))) *
          (σ * Θ (ιA w) * σ⁻¹)⁻¹ := by
    intro w z y hz
    have hιz : ιX z = (ιX x * ιA w * (ιX x)⁻¹) * ιX y * (ιX x * ιA w * (ιX x)⁻¹)⁻¹ := by
      apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hιX, hιA]
      exact hz
    rw [← F1 z, hιz, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, F1 y, F1 x, hxσ]
  have hDY : oTwoIn X ≤ Subgroup.normalizer (Y : Set G) :=
    h.oTwoIn_le_pCore.trans h.pCore_le_normalizer_Y
  have hD2 : IsPGroup 2 ↥(oTwoIn X) := isPGroup_oTwoIn X
  have hNXa : ∀ g ∈ A, (x : G) * g * (x : G)⁻¹ ∈ Subgroup.normalizer (X : Set G) := fun g hg =>
    mul_mem (mul_mem (Subgroup.le_normalizer x.2) (hAN hg))
      (inv_mem (Subgroup.le_normalizer x.2))
  have hYstab : ∀ y : ↥X, (y : G) ∈ Y → toAlt φ y ∈ altStabilizer (2 * a + 1) F := by
    intro y hy
    rw [← himg]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hy))
  have hYlift : ∀ s ∈ altStabilizer (2 * a + 1) F, ∃ w : ↥X, (w : G) ∈ Y ∧ toAlt φ w = s := by
    intro s hs
    rw [← himg] at hs
    obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hs
    exact ⟨w, Subgroup.mem_subgroupOf.mp hw, rfl⟩
  refine ⟨x, x.2, ?_, ?_⟩
  ·
    rintro _ ⟨g, hg, rfl⟩
    show (x : G) * g * (x : G)⁻¹ ∈ Subgroup.normalizer (Y : Set G)
    refine mem_normalizer_of_conj_le_sup h.hNoY hD2 hDY (fun y hy => ?_)
    have hyX : y ∈ X := hYX hy
    have hz : (x : G) * g * (x : G)⁻¹ * y * ((x : G) * g * (x : G)⁻¹)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hNXa g hg) y).mp hyX
    have key := F4 ⟨g, hg⟩ ⟨_, hz⟩ ⟨y, hyX⟩ rfl
    have hτ := hσstab _ (F2 ⟨g, hg⟩)
    generalize σ * Θ (ιA ⟨g, hg⟩) * σ⁻¹ = τ at key hτ
    have hτ' := (setStab Fᶜ).inv_mem hτ
    have hfix : toAlt φ ⟨_, hz⟩ ∈ altStabilizer (2 * a + 1) F := by
      rw [mem_altStabilizer]
      intro ℓ hℓ
      rw [key]
      have h1 : τ⁻¹ ℓ ∈ F := mem_of_mem_setStab_compl hτ' hℓ
      have h2 := (mem_altStabilizer.mp (hYstab ⟨y, hyX⟩ hy)) _ h1
      simp only [Equiv.Perm.mul_apply]
      rw [h2]
      simp
    obtain ⟨w₂, hw₂Y, hw₂⟩ := hYlift _ hfix
    have hmem := (toAlt_eq_iff φ w₂ ⟨_, hz⟩).mp hw₂
    have ho : (((w₂⁻¹ * ⟨_, hz⟩ : ↥X)) : G) ∈ oTwoIn X := ⟨_, hmem, rfl⟩
    have e : (x : G) * g * (x : G)⁻¹ * y * ((x : G) * g * (x : G)⁻¹)⁻¹ =
        (w₂ : G) * (((w₂⁻¹ * ⟨_, hz⟩ : ↥X)) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hw₂Y) (Subgroup.mem_sup_right ho)
  ·
    obtain ⟨w₀, hw₀⟩ := F3
    intro hle
    have hcalt : Equiv.swap i j * Equiv.swap j k ∈ alternatingGroup (Fin (2 * a + 1)) := by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij,
        Equiv.Perm.sign_swap (Ne.symm hkj)]
      decide
    have hcF : (⟨Equiv.swap i j * Equiv.swap j k, hcalt⟩ : alternatingGroup (Fin (2 * a + 1))) ∈
        altStabilizer (2 * a + 1) F := by
      rw [mem_altStabilizer]
      intro ℓ hℓ
      have hℓi : ℓ ≠ i := fun e => (Finset.mem_compl.mp hi) (e ▸ hℓ)
      have hℓj : ℓ ≠ j := fun e => (Finset.mem_compl.mp hj) (e ▸ hℓ)
      have hℓk : ℓ ≠ k := fun e => (Finset.mem_compl.mp hkΩ) (e ▸ hℓ)
      show (Equiv.swap i j * Equiv.swap j k) ℓ = ℓ
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hℓj hℓk,
        Equiv.swap_apply_of_ne_of_ne hℓi hℓj]
    obtain ⟨w₂, hw₂Y, hw₂⟩ := hYlift _ hcF
    have ha₀A : (w₀ : G) ∈ A := w₀.2
    have hyY : (w₂ : G) ∈ Y := hw₂Y
    have ha'mem : (x : G) * (w₀ : G) * (x : G)⁻¹ ∈ A.map (MulAut.conj (x : G)).toMonoidHom :=
      ⟨(w₀ : G), ha₀A, rfl⟩
    have hcomm : ⁅(x : G) * (w₀ : G) * (x : G)⁻¹, (w₂ : G)⁆ ∈
        ⁅A.map (MulAut.conj (x : G)).toMonoidHom, Y⁆ :=
      Subgroup.commutator_mem_commutator ha'mem hyY
    have hz₀ := hle hcomm
    obtain ⟨m, hm⟩ := (isPGroup_oTwoIn Y) ⟨_, hz₀⟩
    have hpow : ⁅(x : G) * (w₀ : G) * (x : G)⁻¹, (w₂ : G)⁆ ^ 2 ^ m = 1 := congrArg Subtype.val hm
    have ha'N := hNXa (w₀ : G) ha₀A
    have hu : (x : G) * (w₀ : G) * (x : G)⁻¹ * (w₂ : G) * ((x : G) * (w₀ : G) * (x : G)⁻¹)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp ha'N (w₂ : G)).mp w₂.2
    have key := F4 w₀ ⟨_, hu⟩ w₂ rfl
    rw [hw₀, hσt₀] at key
    have hc : ((toAlt φ w₂ : alternatingGroup (Fin (2 * a + 1))) :
        Equiv.Perm (Fin (2 * a + 1))) = Equiv.swap i j * Equiv.swap j k := congrArg Subtype.val hw₂
    rw [hc] at key
    have hzX : ⁅(x : G) * (w₀ : G) * (x : G)⁻¹, (w₂ : G)⁆ ∈ X := by
      rw [commutatorElement_def]
      exact X.mul_mem hu (X.inv_mem w₂.2)
    have hv : (⟨_, hzX⟩ : ↥X) = ⟨_, hu⟩ * w₂⁻¹ := Subtype.ext (by simp [commutatorElement_def])
    have h1 : toAlt φ ⟨_, hzX⟩ ^ 2 ^ m = 1 := by
      rw [← map_pow]
      have : (⟨_, hzX⟩ : ↥X) ^ 2 ^ m = 1 := Subtype.ext (by simpa using hpow)
      rw [this, map_one]
    have h2 : ((toAlt φ ⟨_, hzX⟩ : alternatingGroup (Fin (2 * a + 1))) :
        Equiv.Perm (Fin (2 * a + 1))) ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val h1
      simpa using this
    rw [hv, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, key, hc] at h2
    exact swap_commutator_pow_ne_one hij (Ne.symm hki) (Ne.symm hkj) m h2

end CFSG.CGT.PushingUpLit.CGT6
