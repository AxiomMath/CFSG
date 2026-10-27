module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma27
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L27ReentryA5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Irr
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDA5C61

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppD
  CFSG.QuasithinUnique.A5.Delta5 Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem A5Pi.invariant_eq {L : Subgroup G} (P : AppC.A5Pi L) {K : Subgroup G}
    (hKU : K ≤ blockU L) (hK1 : K ≠ ⊥) (hinv : ∀ ℓ ∈ L, ∀ k ∈ K, ℓ * k * ℓ⁻¹ ∈ K) :
    K = blockU L := by
  classical
  let car : Set (Fin 5 → ZMod 2) := {x | ∃ hx : x ∈ evenWeight 5,
    ((P.β.symm (Multiplicative.ofAdd ⟨x, hx⟩) : ↥(blockU L)) : G) ∈ K}
  have hzero : (0 : Fin 5 → ZMod 2) ∈ car := by
    refine ⟨zero_mem _, ?_⟩
    have e : P.β.symm (Multiplicative.ofAdd (⟨0, zero_mem _⟩ : evenWeight 5)) = 1 := by
      rw [← map_one P.β.symm]
      rfl
    rw [e]
    exact K.one_mem
  have hadd : ∀ x ∈ car, ∀ y ∈ car, x + y ∈ car := by
    rintro x ⟨hx, hxK⟩ y ⟨hy, hyK⟩
    refine ⟨add_mem hx hy, ?_⟩
    have e : P.β.symm (Multiplicative.ofAdd (⟨x + y, add_mem hx hy⟩ : evenWeight 5)) =
        P.β.symm (Multiplicative.ofAdd ⟨x, hx⟩) * P.β.symm (Multiplicative.ofAdd ⟨y, hy⟩) := by
      rw [← map_mul]
      rfl
    rw [e]
    exact K.mul_mem hxK hyK
  let W : Submodule (ZMod 2) (Fin 5 → ZMod 2) :=
    { carrier := car
      add_mem' := fun {x y} hx hy => hadd x hx y hy
      zero_mem' := hzero
      smul_mem' := by
        intro c x hx
        have hc : c = 0 ∨ c = 1 := by revert c; decide
        rcases hc with rfl | rfl
        · rw [zero_smul]; exact hzero
        · rw [one_smul]; exact hx }
  have hWd : W ≤ A5.Kc3Irr.delta5 (F := ZMod 2) := by
    intro x hx
    obtain ⟨hxe, -⟩ := hx
    rw [A5.Kc3Irr.mem_delta5]
    exact hxe
  have hLN : ∀ ℓ : G, ℓ ∈ L → ℓ ∈ Subgroup.normalizer (L : Set G) := fun ℓ hℓ =>
    Subgroup.le_normalizer hℓ
  have hinvW : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → ∀ x ∈ W,
      A5.Kc3Irr.pactF σ x ∈ W := by
    intro σ hσ x hx
    obtain ⟨hxe, hxK⟩ := hx
    obtain ⟨ℓ, hℓ⟩ := P.hα ⟨σ, (Equiv.Perm.mem_alternatingGroup).2 hσ⟩
    have hℓL : (ℓ : G) ∈ L := ℓ.2
    have hpe : pact σ x ∈ evenWeight 5 := pact_mem σ hxe
    have hπℓ : P.π ⟨(ℓ : G), hLN _ hℓL⟩ = σ := by
      have := P.hπα (ℓ : G) hℓL
      rw [show (⟨(ℓ : G), hℓL⟩ : ↥L) = ℓ from rfl, hℓ] at this
      exact this
    refine ⟨hpe, ?_⟩
    set u : ↥(blockU L) := P.β.symm (Multiplicative.ofAdd ⟨x, hxe⟩) with hu
    have hu' : (ℓ : G) * (u : G) * (ℓ : G)⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (hLN _ hℓL)) (u : G)).mp u.2
    have hcomp := P.hcomp ⟨(ℓ : G), hLN _ hℓL⟩ u ⟨_, hu'⟩ rfl
    rw [hπℓ] at hcomp
    have hβu : P.β u = Multiplicative.ofAdd ⟨x, hxe⟩ := by rw [hu]; simp
    rw [hβu] at hcomp
    have hu'eq : P.β.symm (Multiplicative.ofAdd (⟨pact σ x, hpe⟩ : evenWeight 5)) = ⟨_, hu'⟩ := by
      rw [MulEquiv.symm_apply_eq]
      apply Multiplicative.toAdd.injective
      exact hcomp.symm
    show ((P.β.symm (Multiplicative.ofAdd (⟨pact σ x, hpe⟩ : evenWeight 5)) : ↥(blockU L)) : G) ∈ K
    rw [hu'eq]
    exact hinv _ hℓL _ hxK
  obtain ⟨⟨k, hkK⟩, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hK1
  have hk1' : k ≠ 1 := fun h => hk1 (Subtype.ext h)
  have hkU : k ∈ blockU L := hKU hkK
  have hWne : W ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    refine ⟨((Multiplicative.toAdd (P.β ⟨k, hkU⟩) : evenWeight 5) : Fin 5 → ZMod 2), ?_, ?_⟩
    · refine ⟨(Multiplicative.toAdd (P.β ⟨k, hkU⟩)).2, ?_⟩
      have e : P.β.symm (Multiplicative.ofAdd (⟨((Multiplicative.toAdd (P.β ⟨k, hkU⟩) :
          evenWeight 5) : Fin 5 → ZMod 2), (Multiplicative.toAdd (P.β ⟨k, hkU⟩)).2⟩ :
          evenWeight 5)) = ⟨k, hkU⟩ := by
        simp
      show ((P.β.symm (Multiplicative.ofAdd (⟨_, (Multiplicative.toAdd (P.β ⟨k, hkU⟩)).2⟩ :
        evenWeight 5)) : ↥(blockU L)) : G) ∈ K
      rw [e]
      exact hkK
    · intro h0
      apply hk1'
      have h1 : Multiplicative.toAdd (P.β ⟨k, hkU⟩) = 0 := Subtype.ext h0
      have h2 : P.β ⟨k, hkU⟩ = 1 := h1
      have h3 : (⟨k, hkU⟩ : ↥(blockU L)) = 1 := by
        apply P.β.injective
        rw [h2, map_one]
      exact congrArg Subtype.val h3
  have hWeq : W = A5.Kc3Irr.delta5 := A5.Kc3Irr.irr_delta5 hWd hinvW hWne
  refine le_antisymm hKU fun u hu => ?_
  have hxd : ((Multiplicative.toAdd (P.β ⟨u, hu⟩) : evenWeight 5) : Fin 5 → ZMod 2) ∈
      (A5.Kc3Irr.delta5 : Submodule (ZMod 2) (Fin 5 → ZMod 2)) := by
    rw [A5.Kc3Irr.mem_delta5]
    exact (Multiplicative.toAdd (P.β ⟨u, hu⟩)).2
  rw [← hWeq] at hxd
  obtain ⟨hx, hxK⟩ := hxd
  have e : P.β.symm (Multiplicative.ofAdd (⟨((Multiplicative.toAdd (P.β ⟨u, hu⟩) :
      evenWeight 5) : Fin 5 → ZMod 2), hx⟩ : evenWeight 5)) = ⟨u, hu⟩ := by
    simp
  rw [e] at hxK
  exact hxK

section Comm

variable {T M H S L : Subgroup G}

omit [Finite G] in
theorem A5Pi.alpha_conj {L : Subgroup G} (P : AppC.A5Pi L) {n ℓ : G}
    (hn : n ∈ Subgroup.normalizer (L : Set G)) (hℓ : ℓ ∈ L) (hnℓ : n * ℓ * n⁻¹ ∈ L) :
    ((P.α ⟨n * ℓ * n⁻¹, hnℓ⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
      P.π ⟨n, hn⟩ * ((P.α ⟨ℓ, hℓ⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) * (P.π ⟨n, hn⟩)⁻¹ := by
  have h1 := P.hπα (n * ℓ * n⁻¹) hnℓ
  have h2 := P.hπα ℓ hℓ
  have e : (⟨n * ℓ * n⁻¹, Subgroup.le_normalizer hnℓ⟩ : ↥(Subgroup.normalizer (L : Set G))) =
      ⟨n, hn⟩ * ⟨ℓ, Subgroup.le_normalizer hℓ⟩ * ⟨n, hn⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, h2] at h1
  exact h1.symm

theorem A5.commutator_eq (C : AppC.Cfg T M H S L) (hQU : blockQ L = blockU L) {x : G}
    {M₀ : Subgroup G} (m : GMate S T M₀ x) : ⁅L, conjR (blockU L) x⁆ = L := by
  have hcs := C.hcs
  have hSH : S ≤ H := hcs.sylow.le
  have hVB : conjR (blockU L) x ≤ baum S := m.V_le_B (GCfg.ofCfg C)
  have hVS : conjR (blockU L) x ≤ S := hVB.trans inf_le_left
  have hVN : conjR (blockU L) x ≤ Subgroup.normalizer (L : Set G) := hVS.trans C.hSN
  have hVnQ : ¬ conjR (blockU L) x ≤ pCoreOf 2 H := m.V_not_le_Q (GCfg.ofCfg C)
  have hUL : blockU L ≤ L := A5.blockU_le_L hcs
  have hLN : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  obtain ⟨v, hvV, hvN, hπv⟩ : ∃ v ∈ conjR (blockU L) x, ∃ hvN : v ∈ Subgroup.normalizer (L : Set G),
      C.P.π ⟨v, hvN⟩ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hVnQ
    intro v hv
    have hvN : v ∈ Subgroup.normalizer (L : Set G) := hVN hv
    have h1 := (C.P.hker ⟨v, hvN⟩).mp (hcon v hv hvN)
    rw [← C.hQ]
    refine ⟨hSH (hVS hv), Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have := h1 u hu
    calc u * v = (v * u * v⁻¹) * v := by rw [this]
      _ = v * u := by group
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup G, N = ⁅L, conjR (blockU L) x⁆ := ⟨_, rfl⟩
  rw [← hNdef]
  have hNL : N ≤ L := by
    rw [hNdef, Subgroup.commutator_le]
    intro l hl a ha
    have h1 : a * l⁻¹ * a⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hVN ha) l⁻¹).mp (inv_mem hl)
    have : ⁅l, a⁆ = l * (a * l⁻¹ * a⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact mul_mem hl h1
  have hLNN : L ≤ Subgroup.normalizer (N : Set G) := by
    rw [hNdef]
    exact Subgroup.normalizer_commutator_ge_left L _
  have hNn : (N.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr hLNN
  have hNα : ((N.subgroupOf L).map C.P.α).Normal := hNn.map C.P.α C.P.hα
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hker : ∀ l : ↥L, C.P.α l = 1 → (l : G) ∈ blockU L := by
    intro l hl
    have h1 : l ∈ C.P.α.ker := hl
    rw [C.P.hαk] at h1
    rw [← hQU]
    show (l : G) ∈ pCoreOf 2 L
    unfold pCoreOf
    exact (Subgroup.mem_map_iff_mem L.subtype_injective).mpr h1
  have hτ : C.P.π ⟨v, hvN⟩ ≠ 1 := hπv
  obtain ⟨a, ha, haτ⟩ : ∃ a : Perm (Fin 5), Perm.sign a = 1 ∧
      C.P.π ⟨v, hvN⟩ * a ≠ a * C.P.π ⟨v, hvN⟩ := by
    by_contra hcon
    push Not at hcon
    exact hτ (cent_alt _ hcon)
  obtain ⟨ℓ, hℓ⟩ := C.P.hα ⟨a, (Equiv.Perm.mem_alternatingGroup).2 ha⟩
  have hℓL : (ℓ : G) ∈ L := ℓ.2
  have hcN : (ℓ : G) * v * (ℓ : G)⁻¹ * v⁻¹ ∈ N := by
    rw [hNdef]
    exact Subgroup.commutator_mem_commutator hℓL hvV
  have hcL : (ℓ : G) * v * (ℓ : G)⁻¹ * v⁻¹ ∈ L := hNL hcN
  have hvℓ : v * (ℓ : G)⁻¹ * v⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hvN _).mp (inv_mem hℓL)
  have hαc : ((C.P.α ⟨(ℓ : G) * v * (ℓ : G)⁻¹ * v⁻¹, hcL⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5))
      = a * C.P.π ⟨v, hvN⟩ * a⁻¹ * (C.P.π ⟨v, hvN⟩)⁻¹ := by
    have e : (⟨(ℓ : G) * v * (ℓ : G)⁻¹ * v⁻¹, hcL⟩ : ↥L) =
        ℓ * ⟨v * (ℓ : G)⁻¹ * v⁻¹, hvℓ⟩ := Subtype.ext (by simp [mul_assoc])
    rw [e, map_mul]
    have h1 := A5Pi.alpha_conj C.P (n := v) (ℓ := (ℓ : G)⁻¹) hvN (inv_mem hℓL) hvℓ
    have e2 : (⟨(ℓ : G)⁻¹, inv_mem hℓL⟩ : ↥L) = ℓ⁻¹ := rfl
    rw [e2, map_inv] at h1
    show ((C.P.α ℓ : alternatingGroup (Fin 5)) : Perm (Fin 5)) *
      ((C.P.α ⟨v * (ℓ : G)⁻¹ * v⁻¹, hvℓ⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) = _
    rw [h1, hℓ]
    simp only [Subgroup.coe_inv]
    group
  have hα1 : C.P.α ⟨(ℓ : G) * v * (ℓ : G)⁻¹ * v⁻¹, hcL⟩ ≠ 1 := by
    intro h1
    apply haτ
    have h2 : ((C.P.α ⟨(ℓ : G) * v * (ℓ : G)⁻¹ * v⁻¹, hcL⟩ : alternatingGroup (Fin 5)) :
        Perm (Fin 5)) = 1 := by rw [h1]; rfl
    rw [hαc] at h2
    have h3 : a * C.P.π ⟨v, hvN⟩ * a⁻¹ * (C.P.π ⟨v, hvN⟩)⁻¹ = 1 := h2
    calc C.P.π ⟨v, hvN⟩ * a = (a * C.P.π ⟨v, hvN⟩ * a⁻¹ * (C.P.π ⟨v, hvN⟩)⁻¹) *
          (C.P.π ⟨v, hvN⟩ * a) := by rw [h3]; group
      _ = a * C.P.π ⟨v, hvN⟩ := by group
  have hαtop : (N.subgroupOf L).map C.P.α = ⊤ := by
    have := hsimple
    have := hNα
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf L).map C.P.α) with h | h
    · exfalso
      apply hα1
      have : C.P.α ⟨(ℓ : G) * v * (ℓ : G)⁻¹ * v⁻¹, hcL⟩ ∈ (N.subgroupOf L).map C.P.α :=
        ⟨⟨_, hcL⟩, hcN, rfl⟩
      rw [h] at this
      exact this
    · exact h
  have hLUN : ∀ l ∈ L, ∃ n ∈ N, l * n⁻¹ ∈ blockU L := by
    intro l hl
    have hmem : C.P.α ⟨l, hl⟩ ∈ (N.subgroupOf L).map C.P.α := by rw [hαtop]; trivial
    obtain ⟨n', hn', hn'α⟩ := hmem
    refine ⟨(n' : G), hn', ?_⟩
    have h1 : C.P.α (⟨l, hl⟩ * n'⁻¹) = 1 := by rw [map_mul, map_inv, hn'α]; group
    exact hker _ h1
  have hUab : IsElemAbelian 2 (blockU L) := (GCfg.ofCfg C).hU
  have hKinv : ∀ ℓ ∈ L, ∀ k ∈ N ⊓ blockU L, ℓ * k * ℓ⁻¹ ∈ N ⊓ blockU L := fun ℓ hℓ k hk =>
    ⟨(Subgroup.mem_normalizer_iff.mp (hLNN hℓ) k).mp hk.1,
      (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (hLN hℓ)) k).mp hk.2⟩
  have hK1 : N ⊓ blockU L ≠ ⊥ := by
    intro hK
    have hNU : ∀ n ∈ N, ∀ u ∈ blockU L, n * u = u * n := by
      intro n hn u hu
      have hnL : n ∈ L := hNL hn
      have h1 : n * u * n⁻¹ * u⁻¹ ∈ blockU L := by
        have := (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (hLN hnL)) u).mp hu
        exact mul_mem this (inv_mem hu)
      have h2 : n * u * n⁻¹ * u⁻¹ ∈ N := by
        have h3 : u * n⁻¹ * u⁻¹ ∈ N :=
          (Subgroup.mem_normalizer_iff.mp (hLNN (hUL hu)) n⁻¹).mp (inv_mem hn)
        have : n * u * n⁻¹ * u⁻¹ = n * (u * n⁻¹ * u⁻¹) := by group
        rw [this]
        exact mul_mem hn h3
      have h4 : n * u * n⁻¹ * u⁻¹ ∈ N ⊓ blockU L := ⟨h2, h1⟩
      rw [hK, Subgroup.mem_bot] at h4
      calc n * u = (n * u * n⁻¹ * u⁻¹) * (u * n) := by group
        _ = u * n := by rw [h4, one_mul]
    have hLU : ∀ l ∈ L, ∀ u ∈ blockU L, l * u = u * l := by
      intro l hl u hu
      obtain ⟨n, hn, hw⟩ := hLUN l hl
      have hl' : l = (l * n⁻¹) * n := by group
      have h1 : (l * n⁻¹) * u = u * (l * n⁻¹) := B2F.isElemAbelian_comm hUab hw hu
      calc l * u = ((l * n⁻¹) * n) * u := by rw [← hl']
        _ = (l * n⁻¹) * (n * u) := by group
        _ = (l * n⁻¹) * (u * n) := by rw [hNU n hn u hu]
        _ = ((l * n⁻¹) * u) * n := by group
        _ = (u * (l * n⁻¹)) * n := by rw [h1]
        _ = u * l := by rw [hl']; group
    have hc3 : swap (2 : Fin 5) 3 * swap 3 4 ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide
    obtain ⟨ℓ₁, hℓ₁⟩ := C.P.hα ⟨_, hc3⟩
    have hℓ₁L : (ℓ₁ : G) ∈ L := ℓ₁.2
    have hπ1 : C.P.π ⟨(ℓ₁ : G), hLN hℓ₁L⟩ = 1 := by
      rw [C.P.hker]
      intro u hu
      have := hLU _ hℓ₁L u hu
      calc (ℓ₁ : G) * u * (ℓ₁ : G)⁻¹ = (u * (ℓ₁ : G)) * (ℓ₁ : G)⁻¹ := by rw [this]
        _ = u := by group
    have h1 := C.P.hπα (ℓ₁ : G) hℓ₁L
    rw [hπ1, show (⟨(ℓ₁ : G), hℓ₁L⟩ : ↥L) = ℓ₁ from rfl, hℓ₁] at h1
    have h2 : (swap (2 : Fin 5) 3 * swap 3 4) = 1 := h1.symm
    exact absurd h2 (by decide)
  have hKU : N ⊓ blockU L = blockU L := A5Pi.invariant_eq C.P inf_le_right hK1 hKinv
  have hUN : blockU L ≤ N := fun u hu => by
    have : u ∈ N ⊓ blockU L := by rw [hKU]; exact hu
    exact this.1
  refine le_antisymm hNL fun l hl => ?_
  obtain ⟨n, hn, hw⟩ := hLUN l hl
  have hl' : l = (l * n⁻¹) * n := by group
  rw [hl']
  exact mul_mem (hUN hw) hn

end Comm

section Gen

variable {T M H S L : Subgroup G}

theorem blockD_inf_sup_conj_gen {C : GCfg T M H S L} {x : G} {M₀ : Subgroup G}
    (m : GMate S T M₀ x) :
    blockD S L ⊓ (C.U ⊔ conjR C.U x) = ⊥ ∧
      ∀ d ∈ blockD S L, ∀ y ∈ C.U ⊔ conjR C.U x, d * y = y * d := by
  have hUn : C.U ≤ Subgroup.normalizer (conjR C.U x : Set G) := C.hUS.trans (m.S_le_N_V C)
  have hinf : blockD S L ⊓ (C.U ⊔ conjR C.U x) = ⊥ := by
    rw [eq_bot_iff]
    rintro t ⟨htD, htY⟩
    have htY' : t ∈ ((C.U ⊔ conjR C.U x : Subgroup G) : Set G) := htY
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hUn] at htY'
    obtain ⟨u, hu, u', hu', htu0⟩ := htY'
    have htu : u * u' = t := htu0
    have hu'Q : u' ∈ pCoreOf 2 H := by
      have : u' = u⁻¹ * t := by rw [← htu]; group
      rw [this]
      exact mul_mem (inv_mem (C.hUQ hu)) (C.D_le_Q htD)
    have hu'U : u' ∈ C.U := m.V_inf_Q_le_U C hu' hu'Q
    have htU : t ∈ C.U := by rw [← htu]; exact mul_mem hu hu'U
    have : t ∈ C.U ⊓ blockD S L := ⟨htU, htD⟩
    rw [C.U_inf_D] at this
    exact this
  refine ⟨hinf, fun d hd y hy => ?_⟩
  have hle : C.U ⊔ conjR C.U x ≤ Subgroup.centralizer ({d} : Set G) :=
    sup_le
      (fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr (C.Q_comm_U (C.D_le_Q hd) hu).symm)
      (fun v hv => Subgroup.mem_centralizer_singleton_iff.mpr (m.D_comm_V C hd hv).symm)
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm

end Gen

theorem lemma2_4_27A5_of
    (h27_1 : Lemma2_4_27_1A5) : Lemma2_4_27A5 := by
  intro G _ _ T M H S L hcs h5 hj
  obtain ⟨C⟩ := AppC.nonempty_cfg hcs hj h5
  obtain ⟨hidx, hbJ, hJT⟩ := h27_1 G T M H S L hcs h5 hj
  have hTN : T ≤ Subgroup.normalizer (S : Set G) := normalizer_of_relIndex_two hcs.le_T hidx
  obtain ⟨hU0, hDab, hbD, hQ, -, -, hx⟩ :=
    AppC.c56A5Case G T M H S L hcs h5 hj T hcs.le_T le_rfl hidx
  have hQ' : pCoreOf 2 H = blockD S L ⊔ blockU0 S L := by rw [← hbD]; exact hQ
  have hU0eq : blockU0 S L = blockU L := A5.blockU0_eq_blockU hj
  have hUL : blockU L ≤ L := A5.blockU_le_L hcs
  have hUbot : blockU L ≠ ⊥ := fun h => by
    have := (GCfg.ofCfg C).card_U
    rw [show (GCfg.ofCfg C).U = blockU L from rfl, h, Subgroup.card_bot] at this
    omega
  have hTC : blockTC T S L = blockD S L := blockTC_eq_blockD hcs hU0 hQ hUbot hUL
  have hDab' : IsElemAbelian 2 (blockD S L) := hbD ▸ hDab
  have hQU : blockQ L = blockU L := by
    have h1 := hU0
    rw [hU0eq, hj] at h1
    exact h1.symm
  refine ⟨⟨hidx, hbJ, hJT⟩, ?_, ?_, ?_⟩
  ·
    intro x hxT hxS r hrS hrB
    obtain ⟨-, -, hC4, -, -⟩ := AppD.c61_a5 hcs h5 hj
    have hxN : x ∈ normT T S := ⟨hxT, hTN hxT⟩
    obtain ⟨A₁, hA₁, hAmax⟩ := hC4 (Or.inl ⟨h5, hj⟩) x hxN hxS r hrS (by rw [← hbJ]; exact hrB)
    refine ⟨A₁, hA₁, fun B => ?_⟩
    have hJle : thompsonJ T ≤ S := hJT ▸ thompsonJ_le_self S
    exact (isMaxElemAbelian_iff_of_thompsonJ_le hcs.le_T hJle).symm.trans (hAmax B)
  ·
    rw [hTC]
    refine ⟨hDab', hQ', ?_, ?_⟩
    · rw [hU0eq, inf_comm]
      exact (GCfg.ofCfg C).U_inf_D
    · intro x hxT hxS
      have := (hx x hxT hxS).1
      rwa [hbD] at this
  ·
    intro x hxT hxS
    rw [hTC]
    obtain ⟨-, hbaum, -⟩ := hx x hxT hxS
    have m : GMate S T T x := ⟨hcs.le_T, le_rfl, hidx, hxT, hxS⟩
    have hinf := blockD_inf_sup_conj_gen (C := GCfg.ofCfg C) m
    rw [hU0eq] at hbaum ⊢
    refine ⟨?_, hinf.1, hinf.2, ?_⟩
    · have h1 : baum S = baumD S L ⊔ (blockU L ⊔ conjR (blockU L) x) :=
        hbaum.trans (sup_assoc _ _ _)
      rw [hbD] at h1
      exact h1
    · rw [hj]
      exact A5.commutator_eq C hQU m

theorem lemma2_4_27_of
    (hSA : ConstrainedSetupAt) (hlin : Lin2BlockExcluded)
    (ha3 : SingleA3Excluded) (h25 : A5BlockS1) : Lemma2_4_27 :=
  lemma2_4_27_of_cases (lemma2_4_27A5_of (lemma2_4_27_1A5_of hSA hlin ha3 h25))
    (lemma2_4_27A3 (lemma2_4_27_1A3_of hSA hlin ha3 h25))

end CFSG.QuasithinUnique.DoubleA3
