module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsONLoc
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26SCON
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.Native.ONTriple CFSG.Open Subgroup
open scoped commutatorElement

theorem i271on_fix_of_comm {S : Type*} [Group S] (hcen : Subgroup.center S = ⊥) {σ : MulAut S}
    {x : S} (h : σ * MulAut.conj x = MulAut.conj x * σ) : σ x = x := by
  have h1 : MulAut.conj (σ x) = MulAut.conj x := by
    ext y
    have := congrArg (fun τ : MulAut S => τ (σ.symm y)) h
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply] at this
    simpa [MulAut.conj_apply] using this
  exact i271on_conj_injective hcen h1

theorem i271on_mem_normalizer {G : Type*} [Group G] {T : Subgroup G} {g : G}
    (h1 : ∀ t ∈ T, g * t * g⁻¹ ∈ T) (h2 : ∀ t ∈ T, g⁻¹ * t * g ∈ T) :
    g ∈ Subgroup.normalizer (T : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨h1 t, fun ht => ?_⟩
  have := h2 _ ht
  simpa [mul_assoc] using this

section


theorem i271on_R_bot {S : Type} [Group S] [Finite S] (hcen : Subgroup.center S = ⊥)
    (hOut : (MulAut.conj : S →* MulAut S).range.index ∣ 2)
    (hNo : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.NoOuterFixesCentralizer 3 S)
    (q : GM →* S) (hq : Function.Surjective q) (hker : q.ker = zpowers zG)
    {W : Subgroup S} (hW : IsElemAbelian 3 W) (h81 : 81 ≤ Nat.card W)
    {T : Subgroup (MulAut S)} (hT : Nat.Coprime 3 (Nat.card T))
    (hWT : ∀ y ∈ W, (MulAut.conj y : MulAut S) ∈ Subgroup.normalizer (T : Set (MulAut S)))
    {a : GM} {A₀ : Subgroup GM} (hA₀ : CFSG.RankThree.PartTwo.Late.IsE27 A₀) (ha : a ∈ A₀)
    (haz : a ∉ zpowers zG) (hax : q a ∈ W) :
    T ⊓ Subgroup.centralizer ({(MulAut.conj (q a) : MulAut S)} : Set (MulAut S)) = ⊥ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut S) := Finite.of_injective (fun σ : MulAut S => (σ : S → S))
    DFunLike.coe_injective
  obtain ⟨H, ⟨e⟩, hHC, hL2, hCS, E, hEWH, hE9⟩ := i271on_local q hq hker hW h81 hA₀ ha haz hax
  set x : S := q a with hx
  have hxW : x ∈ W := hax
  have hx3 : orderOf x = 3 := i271on_orderOf_q hker (hA₀.1.2 a ha) haz
  set C : Subgroup S := Subgroup.centralizer ({x} : Set S) with hCdef
  set R : Subgroup (MulAut S) :=
    T ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut S)} : Set (MulAut S)) with hR
  have hinj := i271on_conj_injective hcen
  have hRT : R ≤ T := inf_le_left
  have hfix : ∀ σ ∈ R, σ x = x := by
    intro σ hσ
    exact i271on_fix_of_comm hcen
      (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hσ).2)
  have hσC : ∀ σ ∈ R, ∀ c ∈ C, σ c ∈ C := by
    intro σ hσ c hc
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    have := congrArg σ hc
    rw [map_mul, map_mul, hfix σ hσ] at this
    exact this
  set Gen : Set S := {c : S | c ∈ C ∧ Nat.Coprime 3 (orderOf c)} with hGen
  have hHgen : H ≤ Subgroup.closure Gen := by
    intro y hy
    have h1 : (⟨y, hy⟩ : ↥H) ∈ Subgroup.closure {h : ↥H | Nat.Coprime 3 (orderOf h)} := by
      rw [i271on_closure_threePrime e]
      exact Subgroup.mem_top _
    have h2 : y ∈ (Subgroup.closure {h : ↥H | Nat.Coprime 3 (orderOf h)}).map H.subtype :=
      ⟨_, h1, rfl⟩
    rw [MonoidHom.map_closure] at h2
    refine (Subgroup.closure_mono ?_) h2
    rintro _ ⟨h, hh, rfl⟩
    refine ⟨hHC h.2, ?_⟩
    show Nat.Coprime 3 (orderOf (h : S))
    rw [Subgroup.orderOf_coe]
    exact hh
  have hσH : ∀ σ ∈ R, ∀ y ∈ H, σ y ∈ H := by
    intro σ hσ y hy
    have hy' := hHgen hy
    have : σ y ∈ (Subgroup.closure Gen).map σ.toMonoidHom := ⟨y, hy', rfl⟩
    rw [MonoidHom.map_closure] at this
    refine (Subgroup.closure_le H).2 ?_ this
    rintro _ ⟨c, ⟨hcC, hcop⟩, rfl⟩
    refine hL2 _ (hσC σ hσ c hcC) ?_
    show Nat.Coprime 3 (orderOf (σ c))
    rw [MulEquiv.orderOf_eq]
    exact hcop
  have hstab : ∀ σ ∈ R, σ ∈ i271onStab H := by
    intro σ hσ y
    refine ⟨fun hy => ?_, hσH σ hσ y⟩
    have := hσH σ⁻¹ (R.inv_mem hσ) _ hy
    simpa using this
  have hRle : R ≤ i271onStab H := fun σ hσ => hstab σ hσ
  set Rs : Subgroup ↥(i271onStab H) := R.subgroupOf (i271onStab H) with hRs
  set T' : Subgroup (MulAut ↥H) := Rs.map (i271onRes H) with hT'
  have hRscard : Nat.card Rs = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRle).toEquiv
  have hT'cop : Nat.Coprime 3 (Nat.card T') := by
    refine Nat.Coprime.coprime_dvd_right ?_ hT
    refine (Subgroup.card_map_dvd (H := Rs) (i271onRes H)).trans ?_
    rw [hRscard]
    exact Subgroup.card_dvd_of_le hRT
  have hEH : E ≤ H := hEWH.trans inf_le_right
  have hEW : E ≤ W := hEWH.trans inf_le_left
  have hEel : IsElemAbelian 3 E := CFSG.Open.IsElemAbelian.mono hW hEW
  have hEHel : IsElemAbelian 3 (E.subgroupOf H) := CFSG.Open.IsElemAbelian.subgroupOf hEel H
  have hEHcard : Nat.card (E.subgroupOf H) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv
  have hnormR : ∀ y ∈ W, ∀ σ ∈ R,
      (MulAut.conj y : MulAut S) * σ * (MulAut.conj y : MulAut S)⁻¹ ∈ R := by
    intro y hy σ hσ
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (hWT y hy) σ).1 (hRT hσ)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hcy : Commute (MulAut.conj y : MulAut S) (MulAut.conj x) := by
        show MulAut.conj y * MulAut.conj x = MulAut.conj x * MulAut.conj y
        rw [← map_mul, ← map_mul]
        congr 1
        exact congrArg Subtype.val (hW.1.is_comm.comm (⟨y, hy⟩ : ↥W) ⟨x, hxW⟩)
      have hcσ : Commute σ (MulAut.conj x) :=
        Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hσ).2
      exact ((hcy.mul_left hcσ).mul_left hcy.inv_left).eq
  have hnormT' : ∀ f (hf : f ∈ H), f ∈ W → ∀ t' ∈ T',
      (MulAut.conj (⟨f, hf⟩ : ↥H) : MulAut ↥H) * t' *
        (MulAut.conj (⟨f, hf⟩ : ↥H) : MulAut ↥H)⁻¹ ∈ T' := by
    intro f hf hfW t' ht'
    obtain ⟨ρ, hρ, rfl⟩ := ht'
    set γ : ↥(i271onStab H) := ⟨MulAut.conj f, i271on_conj_mem_stab H hf⟩ with hγ
    refine ⟨γ * ρ * γ⁻¹, ?_, ?_⟩
    · show ((γ * ρ * γ⁻¹ : ↥(i271onStab H)) : MulAut S) ∈ R
      have := hnormR f hfW ρ hρ
      simpa [hγ] using this
    · rw [map_mul, map_mul, map_inv, hγ, i271onRes_conj H hf]
  have hT'norm : ∀ g ∈ E.subgroupOf H,
      (MulAut.conj g : MulAut ↥H) ∈ Subgroup.normalizer (T' : Set (MulAut ↥H)) := by
    intro g hg
    have hgE : (g : S) ∈ E := hg
    refine i271on_mem_normalizer (fun t ht => ?_) (fun t ht => ?_)
    · have := hnormT' (g : S) g.2 (hEW hgE) t ht
      simpa using this
    · have hgi : ((g⁻¹ : ↥H) : S) ∈ E := by
        rw [Subgroup.coe_inv]
        exact E.inv_mem hgE
      have := hnormT' ((g⁻¹ : ↥H) : S) (g⁻¹).2 (hEW hgi) t ht
      simp only [Subtype.coe_eta, map_inv, inv_inv] at this
      exact this
  have hT'bot : T' = ⊥ :=
    i271on_balanceH e hEHel (by rw [hEHcard]; exact hE9) hT'cop hT'norm
  have hσid : ∀ σ ∈ R, ∀ y ∈ H, σ y = y := by
    intro σ hσ y hy
    have h1 : i271onRes H ⟨σ, hstab σ hσ⟩ ∈ T' := ⟨_, hσ, rfl⟩
    rw [hT'bot, Subgroup.mem_bot] at h1
    have := congrArg (fun r : MulAut ↥H => ((r ⟨y, hy⟩ : ↥H) : S)) h1
    simpa [i271onRes_apply] using this
  have hinner : ∀ σ ∈ R, σ ∈ (MulAut.conj : S →* MulAut S).range → σ = 1 := by
    rintro σ hσ ⟨τ, rfl⟩
    have hτx : τ * x = x * τ := by
      have h := hfix _ hσ
      simp only [MulAut.conj_apply] at h
      rw [mul_inv_eq_iff_eq_mul] at h
      exact h
    have hτC : τ ∈ C := Subgroup.mem_centralizer_singleton_iff.2 hτx
    have hτH' : ∀ y ∈ H, τ * y * τ⁻¹ = y := by
      intro y hy
      have := hσid _ hσ y hy
      simpa [MulAut.conj_apply] using this
    have hcop : Nat.Coprime 3 (orderOf τ) := by
      have h1 : orderOf (MulAut.conj τ : MulAut S) = orderOf τ :=
        orderOf_injective _ hinj τ
      have h2 : orderOf (MulAut.conj τ : MulAut S) ∣ Nat.card T := by
        have := orderOf_dvd_natCard (⟨MulAut.conj τ, hRT hσ⟩ : ↥T)
        rwa [Subgroup.orderOf_mk] at this
      rw [← h1]
      exact Nat.Coprime.coprime_dvd_right h2 hT
    have hτH : τ ∈ H := hL2 τ hτC hcop
    have hz : (⟨τ, hτH⟩ : ↥H) ∈ Subgroup.center ↥H := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      show (y : S) * τ = τ * y
      have := hτH' y y.2
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    rw [i271on_alt_center e, Subgroup.mem_bot] at hz
    have : τ = 1 := congrArg Subtype.val hz
    rw [this, map_one]
  set I : Subgroup (MulAut S) := (MulAut.conj : S →* MulAut S).range with hI
  haveI hInorm : I.Normal := i2326o_normal_inner
  have hindex : I.index ≤ 2 := Nat.le_of_dvd (by norm_num) hOut
  have hRinj : ∀ σ ∈ R, σ ∈ I → σ = 1 := fun σ hσ hσI => hinner σ hσ hσI
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  by_contra hσ1
  have hσI : σ ∉ I := fun h => hσ1 (hRinj σ hσ h)
  have hσ2 : σ ^ 2 = 1 := by
    have h1 := Subgroup.pow_index_mem I σ
    obtain ⟨c, hc⟩ := hOut
    have h2 : σ ^ 2 ∈ I := by
      rw [hc, pow_mul]
      exact Subgroup.pow_mem _ h1 c
    exact hRinj _ (R.pow_mem hσ 2) h2
  have hRσ : ∀ σ' ∈ R, σ' = 1 ∨ σ' = σ := by
    intro σ' hσ'
    by_cases hσ'I : σ' ∈ I
    · exact Or.inl (hRinj σ' hσ' hσ'I)
    · right
      have hcard : Nat.card (MulAut S ⧸ I) ≤ 2 := by
        have : Nat.card (MulAut S ⧸ I) = I.index := rfl
        omega
      have hne : ∀ τ : MulAut S, τ ∉ I → (QuotientGroup.mk τ : MulAut S ⧸ I) ≠ 1 := by
        intro τ hτ h
        exact hτ ((QuotientGroup.eq_one_iff τ).1 h)
      have hmk := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.eq_of_ne_one_of_card_le_two hcard
        (hne σ' hσ'I) (hne σ hσI)
      have h1 : σ⁻¹ * σ' ∈ I := by
        have := (QuotientGroup.eq (a := σ) (b := σ')).1 hmk.symm
        exact this
      have h2 : σ⁻¹ * σ' ∈ R := R.mul_mem (R.inv_mem hσ) hσ'
      have h3 := hRinj _ h2 h1
      exact (inv_mul_eq_one.1 h3).symm
  have hσW : ∀ y ∈ W, σ y = y := by
    intro y hy
    have h1 := hnormR y hy σ hσ
    have h2 : (MulAut.conj y : MulAut S) * σ * (MulAut.conj y : MulAut S)⁻¹ ≠ 1 := by
      intro h
      apply hσ1
      have := congrArg (fun τ => (MulAut.conj y : MulAut S)⁻¹ * τ * (MulAut.conj y : MulAut S)) h
      simpa [mul_assoc] using this
    have h3 : (MulAut.conj y : MulAut S) * σ * (MulAut.conj y : MulAut S)⁻¹ = σ :=
      (hRσ _ h1).resolve_left h2
    apply i271on_fix_of_comm hcen
    have : (MulAut.conj y : MulAut S) * σ = σ * MulAut.conj y := by
      rw [mul_inv_eq_iff_eq_mul] at h3
      exact h3
    exact this.symm
  have hWC : W ≤ C := by
    intro w hw
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hW.1.is_comm.comm (⟨w, hw⟩ : ↥W) ⟨x, hxW⟩)
  have hHWC : H ⊔ W ≤ C := sup_le hHC hWC
  have h360 : Nat.card H = 360 := i271on_alt_card e
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3)).1 hW.isPGroup
  have hk4 : 4 ≤ k := by
    by_contra hlt
    have : Nat.card W ≤ 3 ^ 3 := by
      rw [hk]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h81d : 81 ∣ Nat.card W := by
    rw [hk]
    exact (pow_dvd_pow 3 hk4 : 3 ^ 4 ∣ 3 ^ k)
  have hd1 : 360 ∣ Nat.card ↥(H ⊔ W) := h360 ▸ Subgroup.card_dvd_of_le le_sup_left
  have hd2 : 81 ∣ Nat.card ↥(H ⊔ W) := h81d.trans (Subgroup.card_dvd_of_le le_sup_right)
  have hd3 : 3240 ∣ Nat.card ↥(H ⊔ W) := by
    have := Nat.lcm_dvd hd1 hd2
    have h : Nat.lcm 360 81 = 3240 := by norm_num
    rwa [h] at this
  have hle1 : Nat.card ↥(H ⊔ W) ≤ Nat.card C := Subgroup.card_le_of_le hHWC
  have hHWeq : H ⊔ W = C := by
    refine Subgroup.eq_of_le_of_card_ge hHWC ?_
    have := Nat.le_of_dvd Nat.card_pos hd3
    omega
  have hfixC : C ≤ i271onFix σ := by
    rw [← hHWeq]
    refine sup_le ?_ ?_
    · intro y hy
      exact hσid σ hσ y hy
    · intro y hy
      exact hσW y hy
  obtain ⟨t, hxt, hσt⟩ := hNo σ hσ2 hσI x hx3
  apply hσt
  exact hfixC (Subgroup.mem_centralizer_singleton_iff.2 hxt.symm)

end

end CFSG.HardMathSupport.Solomon.Coordinator
