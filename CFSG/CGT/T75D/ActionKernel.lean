module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIFusion

public section

namespace CFSG.CGT.T75D

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G}

@[expose] def kerA (T T₁ : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ Subgroup.normalizer (T : Set G) ∧
    ∀ t ∈ T, x * t * x⁻¹ * t⁻¹ ∈ secA T T₁}
  mul_mem' := by
    rintro x y ⟨hx, hxk⟩ ⟨hy, hyk⟩
    refine ⟨(Subgroup.normalizer (T : Set G)).mul_mem hx hy, fun t ht => ?_⟩
    have h1 := hyk t ht
    have h2 := hxk t ht
    have h3 : x * (y * t * y⁻¹ * t⁻¹) * x⁻¹ ∈ secA T T₁ := by
      have := conj_mem_conjSubgroup x h1
      rwa [conjSubgroup_secA hx] at this
    have e : x * y * t * (x * y)⁻¹ * t⁻¹ =
        (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹) * (x * t * x⁻¹ * t⁻¹) := by group
    rw [e]
    exact (secA T T₁).mul_mem h3 h2
  one_mem' := ⟨Subgroup.one_mem _, fun t _ => by simp⟩
  inv_mem' := by
    rintro x ⟨hx, hxk⟩
    refine ⟨(Subgroup.normalizer (T : Set G)).inv_mem hx, fun t ht => ?_⟩
    have ht' : x⁻¹ * t * x ∈ T := by
      have := conj_mem_of_mem_normalizer ((Subgroup.normalizer (T : Set G)).inv_mem hx) ht
      simpa using this
    have h1 := hxk (x⁻¹ * t * x) ht'
    have e : x⁻¹ * t * x⁻¹⁻¹ * t⁻¹ =
        (x * (x⁻¹ * t * x) * x⁻¹ * (x⁻¹ * t * x)⁻¹)⁻¹ := by group
    rw [e]
    exact (secA T T₁).inv_mem h1

theorem left_le_kerA (hT : IsElemAbelian 2 T) : T ≤ kerA T T₁ := fun x hx =>
  ⟨Subgroup.le_normalizer hx, fun t ht => by
    have : x * t * x⁻¹ * t⁻¹ = 1 := by rw [elemAbelian_mul_comm hT hx ht]; group
    rw [this]
    exact (secA T T₁).one_mem⟩

@[expose] def kerK (T T₁ : Subgroup G) : Subgroup (NQuot T) := barSub T (kerA T T₁)

theorem mem_kerK_iff (hT : IsElemAbelian 2 T) {x : G} (hx : x ∈ Subgroup.normalizer (T : Set G)) :
    barElt T hx ∈ kerK T T₁ ↔ x ∈ kerA T T₁ := by
  constructor
  · intro h
    obtain ⟨u, huN, huK, hux⟩ := (barElt_mem_barSub_iff hx).1 h
    have : x = u * (u⁻¹ * x) := by group
    rw [this]
    exact (kerA T T₁).mul_mem huK (left_le_kerA hT hux)
  · intro h
    exact barElt_mem_barSub hx h

@[expose] noncomputable def actT (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) : NQuot T →* MulAut ↥T :=
  QuotientGroup.lift (T.subgroupOf (Subgroup.normalizer (T : Set G))) T.normalizerMonoidHom (by
    intro x hx
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_iff]
    intro t ht
    exact hT t ht x (Subgroup.mem_subgroupOf.1 hx))

theorem actT_apply (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) {y : G}
    (hy : y ∈ Subgroup.normalizer (T : Set G)) (t : ↥T) :
    ((actT hT (barElt T hy) t : ↥T) : G) = y * t * y⁻¹ := rfl

theorem ker_actT_le (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) :
    (actT hT).ker ≤ kerK T T₁ := by
  intro xb hxb
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective xb
  have hy : (y : G) ∈ Subgroup.normalizer (T : Set G) := y.2
  have hbar : (QuotientGroup.mk y : NQuot T) = barElt T hy := rfl
  rw [hbar] at hxb ⊢
  refine barElt_mem_barSub hy ⟨hy, fun t ht => ?_⟩
  have h1 := congrArg (fun φ : MulAut ↥T => ((φ ⟨t, ht⟩ : ↥T) : G)) (MonoidHom.mem_ker.1 hxb)
  simp only [actT_apply, MulAut.one_apply] at h1
  have : (y : G) * t * (y : G)⁻¹ * t⁻¹ = 1 := by rw [h1]; group
  rw [this]
  exact (secA T T₁).one_mem

section Two

variable [Finite G]

theorem commutator_lt_of_pGroup {p : ℕ} [Fact p.Prime] {T P : Subgroup G} (hP : IsPGroup p P)
    (hTP : T ≤ P) (hPN : P ≤ Subgroup.normalizer (T : Set G)) (hT : T ≠ ⊥) : ⁅T, P⁆ < T := by
  have hle : ⁅T, P⁆ ≤ T := (Subgroup.le_normalizer_iff_commutator_le_left).mp hPN
  refine lt_of_le_of_ne hle fun heq => hT ?_
  have hnil : Group.IsNilpotent ↥P := hP.isNilpotent
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries P).mp hnil
  have key : ∀ k, T ≤ P.lowerCentralSeries k := by
    intro k
    induction k with
    | zero => exact hTP
    | succ k ih =>
      rw [Subgroup.lowerCentralSeries_succ]
      calc T = ⁅T, P⁆ := heq.symm
        _ ≤ ⁅P.lowerCentralSeries k, P⁆ := Subgroup.commutator_mono ih le_rfl
  rw [eq_bot_iff, ← hn]
  exact key n

theorem le_secA_of_invariant {a : G} {T₂ : Subgroup G} (h : Sec4Hyp T T₁ a T₂) {U : Subgroup G}
    (hUT : U ≤ T)
    (hUinv : ∀ n ∈ Subgroup.normalizer (T : Set G), ∀ u ∈ U, n * u * n⁻¹ ∈ U) (hUne : U ≠ T) :
    U ≤ secA T T₁ := by
  by_contra hcon
  obtain ⟨u, huU, huA⟩ := IsConcreteLE.not_le_iff_exists.1 hcon
  have hlt : secA T T₁ < T := lt_of_le_of_lt secA_le_normIn (h.sec3.cfg.normIn_lt h.pair.conj)
  obtain ⟨s, hsT, hsA⟩ := IsConcreteLE.exists_of_lt hlt
  have hall : ∀ t ∈ T, t ∉ secA T T₁ → t ∈ U := by
    intro t ht htA
    obtain ⟨z, hz, hzu⟩ := secA_transitive h.pair h.glob (hUT huU) huA ht htA
    rw [← hzu]
    exact hUinv z hz u huU
  apply hUne
  refine le_antisymm hUT fun t ht => ?_
  by_cases htA : t ∈ secA T T₁
  · have hs : s ∈ U := hall s hsT hsA
    have hst : s * t ∈ U := by
      refine hall _ (T.mul_mem hsT ht) fun hmem => hsA ?_
      have : s = (s * t) * t⁻¹ := by group
      rw [this]
      exact (secA T T₁).mul_mem hmem ((secA T T₁).inv_mem htA)
    have : t = s⁻¹ * (s * t) := by group
    rw [this]
    exact U.mul_mem (U.inv_mem hs) hst
  · exact hall t ht htA

theorem normal_pGroup_le_kerK {a : G} {T₂ : Subgroup G} (h : Sec4Hyp T T₁ a T₂)
    {𝔓 : Subgroup (NQuot T)} [𝔓.Normal] (h2 : IsPGroup 2 𝔓) : 𝔓 ≤ kerK T T₁ := by
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  have hyN : (y : G) ∈ Subgroup.normalizer (T : Set G) := y.2
  have hbar : (QuotientGroup.mk y : NQuot T) = barElt T hyN := rfl
  rw [hbar] at hx ⊢
  set P : Subgroup G := preBar T 𝔓 with hPdef
  have hTp : IsPGroup 2 T := isPGroup_two_of_isElemAbelian h.pair.wc.1
  have hPp : IsPGroup 2 P := isPGroup_preBar hTp h2
  have hPN : P ≤ Subgroup.normalizer (T : Set G) := preBar_le_normalizer 𝔓
  have hTP : T ≤ P := fun t ht => mem_preBar.2 ⟨Subgroup.le_normalizer ht, by
    rw [(barElt_eq_one_iff _).2 ht]
    exact 𝔓.one_mem⟩
  have hyP : (y : G) ∈ P := mem_preBar.2 ⟨hyN, hx⟩
  have hTne : T ≠ ⊥ := h.sec3.cfg.left_ne_bot
  have hlt := commutator_lt_of_pGroup hPp hTP hPN hTne
  have hPconj : ∀ n ∈ Subgroup.normalizer (T : Set G), ∀ p ∈ P, n * p * n⁻¹ ∈ P := by
    intro n hn p hp
    obtain ⟨hpN, hpb⟩ := mem_preBar.1 hp
    refine mem_preBar.2 ⟨(Subgroup.normalizer (T : Set G)).mul_mem
      ((Subgroup.normalizer (T : Set G)).mul_mem hn hpN)
      ((Subgroup.normalizer (T : Set G)).inv_mem hn), ?_⟩
    have e : barElt T ((Subgroup.normalizer (T : Set G)).mul_mem
        ((Subgroup.normalizer (T : Set G)).mul_mem hn hpN)
        ((Subgroup.normalizer (T : Set G)).inv_mem hn)) =
        barElt T hn * barElt T hpN * (barElt T hn)⁻¹ := rfl
    rw [e]
    exact ‹𝔓.Normal›.conj_mem _ hpb _
  have hUinv : ∀ n ∈ Subgroup.normalizer (T : Set G), ∀ u ∈ ⁅T, P⁆, n * u * n⁻¹ ∈ ⁅T, P⁆ := by
    intro n hn u hu
    have hTc : conjSubgroup n T = T := mem_normalizer_iff_conjSubgroup_eq.1 hn
    have hPc : conjSubgroup n P ≤ P := by
      rintro _ ⟨p, hp, rfl⟩
      exact hPconj n hn p hp
    have hmap : conjSubgroup n ⁅T, P⁆ = ⁅conjSubgroup n T, conjSubgroup n P⁆ :=
      Subgroup.map_commutator _ _ _
    have hle : conjSubgroup n ⁅T, P⁆ ≤ ⁅T, P⁆ := by
      rw [hmap, hTc]
      exact Subgroup.commutator_mono le_rfl hPc
    exact hle (conj_mem_conjSubgroup n hu)
  have hUsec : ⁅T, P⁆ ≤ secA T T₁ :=
    le_secA_of_invariant h ((Subgroup.le_normalizer_iff_commutator_le_left).mp hPN) hUinv hlt.ne
  refine barElt_mem_barSub hyN ⟨hyN, fun t ht => ?_⟩
  have hmem : ⁅t, (y : G)⁆ ∈ ⁅T, P⁆ := Subgroup.commutator_mem_commutator ht hyP
  have hmem' : ⁅(y : G), t⁆ ∈ ⁅T, P⁆ := by
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ hmem
  exact hUsec (by simpa [commutatorElement_def] using hmem')

end Two

end CFSG.CGT.T75D
