module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public import CFSG.GroupTheory.HyperplaneGeneration

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.HardMathSupport.Solomon.LocalBalance
open scoped Pointwise

variable {p : ℕ} {S : Type*} [Group S]

theorem gLAPPrimeCoreOf_eq_bot_of_elemAbelian [Finite S] (hp : p.Prime) {T : Subgroup S}
    (hT : IsElemAbelian p T) {s : S} (hsT : s ∈ T) (hs : orderOf s = p)
    (hB : ∀ B : Subgroup S, B ≤ T → B.relIndex T = p →
      GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set S)) = ⊥)
    (hT0 : GLAPPrimeCoreOf p (Subgroup.centralizer (T : Set S)) = ⊥) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set S)) = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({s} : Set S) with hCdef
  set R := GLAPPrimeCoreOf p C with hRdef
  have hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hT.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hTC : T ≤ C := fun a ha => Subgroup.mem_centralizer_singleton_iff.2 (hcomm a ha s hsT)
  have hRC : R ≤ C := GLAPPrimeCoreOf_le C
  have hnorm : ∀ a ∈ T, ∀ x ∈ R, a * x * a⁻¹ ∈ R := fun a ha x hx =>
    GLAPPrimeCoreOf_conj_mem a (hTC ha) x hx
  have hcop : Nat.Coprime p (Nat.card R) := coprime_card_GLAPPrimeCoreOf hp C
  have hRp : ¬ p ∣ Nat.card R := (hp.coprime_iff_not_dvd).1 hcop
  let act : MulDistribMulAction ↥T ↥R :=
    { smul := fun a x => ⟨a * x * (a : S)⁻¹, hnorm a a.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by
        change (1 : S) * (x : S) * (1 : S)⁻¹ = x
        simp)
      mul_smul := fun a b x => Subtype.ext (by
        change ((a : S) * b) * (x : S) * ((a : S) * b)⁻¹ =
          a * ((b : S) * x * (b : S)⁻¹) * (a : S)⁻¹
        group)
      smul_one := fun a => Subtype.ext (by
        change (a : S) * 1 * (a : S)⁻¹ = 1
        simp)
      smul_mul := fun a x y => Subtype.ext (by
        change (a : S) * ((x : S) * y) * (a : S)⁻¹ = (a * x * (a : S)⁻¹) * (a * y * (a : S)⁻¹)
        group) }
  have : CFSG.IsElementaryAbelian p ↥T :=
    { toIsMulCommutative := hT.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hT.2 x x.2) }
  have : Nontrivial ↥T := ⟨⟨⟨s, hsT⟩, 1, fun h => by
    have : s = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at hs
    exact hp.one_lt.ne hs⟩⟩
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := p) (A := ↥T) (H := ↥R) hRp
  have hfix : ∀ B : Subgroup ↥T, B.index = p → CFSG.fixedPointSubgroup ↥B ↥R = ⊥ := by
    intro B hBi
    set Bs : Subgroup S := B.map T.subtype with hBs
    have hBsT : Bs ≤ T := Subgroup.map_subtype_le _
    have hrel : Bs.relIndex T = p := by
      have h : Bs.subgroupOf T = B :=
        Subgroup.comap_map_eq_self_of_injective T.subtype_injective B
      rw [Subgroup.relIndex, h]
      exact hBi
    rw [eq_bot_iff]
    intro x hx
    have hxR : (x : S) ∈ R := x.2
    have hxB : ∀ b ∈ Bs, b * (x : S) = (x : S) * b := by
      intro b hb
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
      have h1 : (⟨b', hb'⟩ : ↥B) • x = x := hx ⟨b', hb'⟩
      have h2 := congrArg Subtype.val h1
      change (b' : S) * x * (b' : S)⁻¹ = x at h2
      change (b' : S) * x = x * b'
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2
    have hx1 : (x : S) = 1 := by
      by_cases hsB : s ∈ Bs
      ·
        have hle : R ⊓ Subgroup.centralizer (Bs : Set S) ≤
            GLAPPrimeCoreOf p (Subgroup.centralizer (Bs : Set S)) := by
          refine le_GLAPPrimeCoreOf_of_normal inf_le_right ?_
            (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hcop)
          intro g hg y hy
          obtain ⟨hyR, hyB⟩ := Subgroup.mem_inf.1 hy
          have hgs : g ∈ C := by
            rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
            exact (Subgroup.mem_centralizer_iff.1 hg s hsB).symm
          refine Subgroup.mem_inf.2 ⟨GLAPPrimeCoreOf_conj_mem g hgs y hyR, ?_⟩
          rw [Subgroup.mem_centralizer_iff] at hg hyB ⊢
          intro b hb
          have cbg : Commute b g := hg b hb
          have cby : Commute b y := hyB b hb
          exact ((cbg.mul_right cby).mul_right cbg.inv_right).eq
        have hmem := hle (Subgroup.mem_inf.2 ⟨hxR, Subgroup.mem_centralizer_iff.2 hxB⟩)
        rw [hB Bs hBsT hrel] at hmem
        exact Subgroup.mem_bot.1 hmem
      ·
        have hK : T ≤ Bs ⊔ Subgroup.zpowers s := by
          set K := Bs ⊔ Subgroup.zpowers s with hKdef
          have hKT : K ≤ T := sup_le hBsT (Subgroup.zpowers_le.2 hsT)
          have hBK : Bs ≤ K := le_sup_left
          have hmul := Subgroup.relIndex_mul_relIndex Bs K T hBK hKT
          rw [hrel] at hmul
          have hprime : (Bs.relIndex K * K.relIndex T).Prime := hmul ▸ hp
          rcases Nat.prime_mul_iff.1 hprime with ⟨-, h1⟩ | ⟨-, h1⟩
          · rw [Subgroup.relIndex_eq_one] at h1
            exact h1
          · exfalso
            rw [Subgroup.relIndex_eq_one] at h1
            exact hsB (h1 (le_sup_right (a := Bs) (Subgroup.mem_zpowers s)))
        have hxs : (x : S) * s = s * x := by
          have := Subgroup.mem_centralizer_singleton_iff.1 (hRC hxR)
          exact this
        have hxT : ∀ t ∈ T, t * (x : S) = (x : S) * t := by
          have hle2 : Bs ⊔ Subgroup.zpowers s ≤ Subgroup.centralizer ({(x : S)} : Set S) := by
            refine sup_le ?_ ?_
            · intro b hb
              exact Subgroup.mem_centralizer_singleton_iff.2 (hxB b hb)
            · refine Subgroup.zpowers_le.2 ?_
              exact Subgroup.mem_centralizer_singleton_iff.2 hxs.symm
          intro t ht
          exact Subgroup.mem_centralizer_singleton_iff.1 (hle2 (hK ht))
        have hle : R ⊓ Subgroup.centralizer (T : Set S) ≤
            GLAPPrimeCoreOf p (Subgroup.centralizer (T : Set S)) := by
          refine le_GLAPPrimeCoreOf_of_normal inf_le_right ?_
            (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hcop)
          intro g hg y hy
          obtain ⟨hyR, hyB⟩ := Subgroup.mem_inf.1 hy
          have hgs : g ∈ C := by
            rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
            exact (Subgroup.mem_centralizer_iff.1 hg s hsT).symm
          refine Subgroup.mem_inf.2 ⟨GLAPPrimeCoreOf_conj_mem g hgs y hyR, ?_⟩
          rw [Subgroup.mem_centralizer_iff] at hg hyB ⊢
          intro b hb
          have cbg : Commute b g := hg b hb
          have cby : Commute b y := hyB b hb
          exact ((cbg.mul_right cby).mul_right cbg.inv_right).eq
        have hmem := hle (Subgroup.mem_inf.2 ⟨hxR, Subgroup.mem_centralizer_iff.2 hxT⟩)
        rw [hT0] at hmem
        exact Subgroup.mem_bot.1 hmem
    exact Subgroup.mem_bot.2 (Subtype.ext hx1)
  have hbot : ∀ B : Subgroup ↥T, ⨆ (_ : B.index = p), CFSG.fixedPointSubgroup ↥B ↥R = ⊥ := by
    intro B
    by_cases h : B.index = p
    · simp [h, hfix B h]
    · simp [h]
  have htop : (⊤ : Subgroup ↥R) = ⊥ := by
    rw [← hgen]
    simp [hbot]
  rw [eq_bot_iff]
  intro y hy
  have : (⟨y, hy⟩ : ↥R) ∈ (⊤ : Subgroup ↥R) := Subgroup.mem_top _
  rw [htop] at this
  exact congrArg Subtype.val (Subgroup.mem_bot.1 this)

theorem oPrimeCoreTrivialAt_of_elemAbelian_sylow [Finite S] (hp : p.Prime) (T : Sylow p S)
    (hT : IsElemAbelian p (T : Subgroup S))
    (hB : ∀ B : Subgroup S, B ≤ T → B.relIndex T = p →
      GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set S)) = ⊥)
    (hT0 : GLAPPrimeCoreOf p (Subgroup.centralizer ((T : Subgroup S) : Set S)) = ⊥) :
    OPrimeCoreTrivialAt p S := by
  have : Fact p.Prime := ⟨hp⟩
  intro s hs
  have hsp : IsPGroup p (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨Q, hQ⟩ := hsp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S Q T
  have hsT : g * s * g⁻¹ ∈ (T : Subgroup S) := by
    have h1 : s ∈ (Q : Subgroup S) := hQ (Subgroup.mem_zpowers s)
    have h2 : MulAut.conj g s ∈ (MulAut.conj g • (Q : Set S)) := Set.smul_mem_smul_set h1
    rw [← Sylow.coe_smul, hg] at h2
    have h3 : g * s * g⁻¹ ∈ T := by simpa [MulAut.conj_apply] using h2
    exact h3
  have hs' : orderOf (g * s * g⁻¹) = p := by
    have := (MulAut.conj g : S ≃* S).orderOf_eq s
    simpa [MulAut.conj_apply, hs] using this
  refine (gLAPPrimeCoreOf_centralizer_conj g s).1 ?_
  exact gLAPPrimeCoreOf_eq_bot_of_elemAbelian hp hT hsT hs' hB hT0

@[expose] def ElemAbelianCover (p : ℕ) (S : Type*) [Group S] : Prop :=
  ∀ s : S, orderOf s = p → ∃ E : Subgroup S, IsElemAbelian p E ∧ s ∈ E ∧
    (∀ B : Subgroup S, B ≤ E → B.relIndex E = p →
      GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set S)) = ⊥) ∧
    GLAPPrimeCoreOf p (Subgroup.centralizer (E : Set S)) = ⊥

theorem oPrimeCoreTrivialAt_of_elemAbelianCover [Finite S] (hp : p.Prime)
    (h : ElemAbelianCover p S) : OPrimeCoreTrivialAt p S := by
  intro s hs
  obtain ⟨E, hE, hsE, hB, hE0⟩ := h s hs
  exact gLAPPrimeCoreOf_eq_bot_of_elemAbelian hp hE hsE hs hB hE0

theorem sylow_comm_of_exists [Finite S] (hp : p.Prime) (T0 : Sylow p S)
    (h0 : ∀ a ∈ (T0 : Subgroup S), ∀ b ∈ (T0 : Subgroup S), a * b = b * a)
    (T : Sylow p S) : ∀ a ∈ (T : Subgroup S), ∀ b ∈ (T : Subgroup S), a * b = b * a := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S T T0
  have hconj : ∀ a ∈ (T : Subgroup S), g * a * g⁻¹ ∈ (T0 : Subgroup S) := by
    intro a ha
    have h2 : MulAut.conj g a ∈ (MulAut.conj g • (T : Set S)) := Set.smul_mem_smul_set ha
    rw [← Sylow.coe_smul, hg] at h2
    have h3 : g * a * g⁻¹ ∈ T0 := by simpa [MulAut.conj_apply] using h2
    exact h3
  intro a ha b hb
  have := h0 _ (hconj a ha) _ (hconj b hb)
  have h4 : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
    calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      _ = (g * b * g⁻¹) * (g * a * g⁻¹) := this
      _ = g * (b * a) * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h4)

theorem noOuterFixesCentralizer_of_abelian_sylow [Finite S] (hp : p.Prime)
    (hab : ∀ T : Sylow p S, ∀ a ∈ (T : Subgroup S), ∀ b ∈ (T : Subgroup S), a * b = b * a)
    (h : ∀ σ : MulAut S, σ ^ 2 = 1 → σ ∉ innerAut S → ∀ T : Sylow p S,
      ∃ x ∈ (T : Subgroup S), σ x ≠ x) : NoOuterFixesCentralizer p S := by
  have : Fact p.Prime := ⟨hp⟩
  intro σ hσ2 hσ s hs
  have hsp : IsPGroup p (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨Q, hQ⟩ := hsp.exists_le_sylow
  obtain ⟨x, hx, hσx⟩ := h σ hσ2 hσ Q
  exact ⟨x, hab Q s (hQ (Subgroup.mem_zpowers s)) x hx, hσx⟩

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
