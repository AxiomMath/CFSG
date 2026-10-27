module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16UNorm
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Lift

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup Matrix

variable {G : Type} [Group G]

theorem O6NatData.card_V {n : ℕ} {L V : Subgroup G} (d : O6NatData G n L V) :
    Nat.card ↥V = 2 ^ (6 * n) := by
  have h1 : Nat.card ↥V = Nat.card (Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F)) :=
    Nat.card_congr (Equiv.ofBijective d.φ d.φ_bij)
  have h2 : Nat.card (Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F)) =
      Nat.card d.F ^ 6 := by
    rw [Nat.card_congr (Multiplicative.toAdd :
      Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F) ≃
        (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F))]
    simp [Nat.card_pi]
  rw [h1, h2, d.card_F, ← pow_mul, mul_comm]

section Act

variable {n : ℕ} {L V : Subgroup G} (d : O6NatData G n L V)

@[expose] noncomputable def O6NatData.eqv : ↥V ≃ (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F) :=
  (MulEquiv.ofBijective d.φ d.φ_bij).toEquiv.trans Multiplicative.toAdd

theorem O6NatData.eqv_apply (v : ↥V) : d.eqv v = Multiplicative.toAdd (d.φ v) := rfl

theorem O6NatData.eqv_mul (v w : ↥V) : d.eqv (v * w) = d.eqv v + d.eqv w := by
  rw [O6NatData.eqv_apply, O6NatData.eqv_apply, O6NatData.eqv_apply, map_mul, toAdd_mul]

@[expose] noncomputable def O6NatData.act (m : G) (hm : m ∈ normalizer (V : Set G)) :
    Equiv.Perm (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F) :=
  d.eqv.permCongr (conjOn V m hm).toEquiv

theorem O6NatData.act_eqv (m : G) (hm : m ∈ normalizer (V : Set G)) (v : ↥V) :
    d.act m hm (d.eqv v) = d.eqv (conjOn V m hm v) := by
  simp [O6NatData.act, Equiv.permCongr_apply]

theorem O6NatData.act_add (m : G) (hm : m ∈ normalizer (V : Set G))
    (x y : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F) :
    d.act m hm (x + y) = d.act m hm x + d.act m hm y := by
  obtain ⟨v, rfl⟩ := d.eqv.surjective x
  obtain ⟨w, rfl⟩ := d.eqv.surjective y
  rw [← d.eqv_mul, d.act_eqv, d.act_eqv, d.act_eqv, ← d.eqv_mul, map_mul]

@[expose] noncomputable def O6NatData.rho (A : Subgroup G) (hA : A ≤ normalizer (V : Set G)) :
    ↥A →* Equiv.Perm (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F) where
  toFun a := d.act a.1 (hA a.2)
  map_one' := Equiv.ext fun x => by
    obtain ⟨v, rfl⟩ := d.eqv.surjective x
    show d.act _ _ (d.eqv v) = d.eqv v
    rw [d.act_eqv]
    exact congrArg d.eqv (Subtype.ext (by simp))
  map_mul' a b := Equiv.ext fun x => by
    obtain ⟨v, rfl⟩ := d.eqv.surjective x
    show d.act _ _ (d.eqv v) = d.act _ _ (d.act _ _ (d.eqv v))
    rw [d.act_eqv, d.act_eqv, d.act_eqv]
    exact congrArg d.eqv (Subtype.ext (by simp [mul_assoc]))

theorem O6NatData.rho_apply (A : Subgroup G) (hA : A ≤ normalizer (V : Set G)) (a : ↥A) :
    d.rho A hA a = d.act a.1 (hA a.2) := rfl

theorem O6NatData.rho_eqv (A : Subgroup G) (hA : A ≤ normalizer (V : Set G)) (a : ↥A)
    (v : ↥V) : d.rho A hA a (d.eqv v) = d.eqv (conjOn V a.1 (hA a.2) v) :=
  d.act_eqv a.1 (hA a.2) v

theorem O6NatData.eps_eqv {l : G} (hl : l ∈ L) (hlV : l ∈ normalizer (V : Set G)) (v : ↥V) :
    ((d.ε ⟨l, hl⟩ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) *ᵥ
      d.eqv v = d.eqv (conjOn V l hlV v) := by
  have h := d.equiv ⟨l, hl⟩ v (conjOn V l hlV v) rfl
  have := congrArg Multiplicative.toAdd h
  rw [toAdd_ofAdd] at this
  exact this.symm

theorem O6NatData.act_eps {l m : G} (hl : l ∈ L) (hlV : l ∈ normalizer (V : Set G))
    (hml : m * l * m⁻¹ ∈ L) (hmlV : m * l * m⁻¹ ∈ normalizer (V : Set G))
    (hm : m ∈ normalizer (V : Set G)) (x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F) :
    d.act m hm (((d.ε ⟨l, hl⟩ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) *ᵥ x) =
      ((d.ε ⟨m * l * m⁻¹, hml⟩ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) *ᵥ
        d.act m hm x := by
  obtain ⟨v, rfl⟩ := d.eqv.surjective x
  rw [d.eps_eqv hl hlV, d.act_eqv, d.act_eqv, d.eps_eqv hml hmlV]
  exact congrArg d.eqv (Subtype.ext (by simp [mul_assoc]))

end Act

theorem O6NatData.exists_lift_fixing {n p : ℕ} {M L V : Subgroup G} [Finite G]
    (d : O6NatData G n L V) (hp : p.Prime) (hp2 : p ≠ 2) (hLM : L ≤ M)
    (hMV : M ≤ normalizer (V : Set G)) {v : G} (hv : v ∈ V) {k : ℕ}
    (E : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F))
    (hE : E ≤ StatedOmega (StatedQuadMinus 3 d.F d.b d.c)) (hEa : IsElemAbelian p E)
    (hk : Nat.card E = p ^ k)
    (hfix : ∀ g ∈ E, ((g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) *ᵥ
      Multiplicative.toAdd (d.φ ⟨v, hv⟩) = Multiplicative.toAdd (d.φ ⟨v, hv⟩)) :
    ∃ S : Subgroup G, S ≤ M ⊓ centralizer ({v} : Set G) ∧ IsElemAbelian p S ∧
      Nat.card S = p ^ k := by
  set f : ↥L →* GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F :=
    (StatedOmega (StatedQuadMinus 3 d.F d.b d.c)).subtype.comp d.ε with hf
  have hker : IsPGroup 2 ↥f.ker := by
    have h : f.ker = CFSG.pCore 2 ↥L := by
      rw [hf, MonoidHom.ker_comp_of_injective _ _
        (StatedOmega (StatedQuadMinus 3 d.F d.b d.c)).subtype_injective, d.ε_ker]
    rw [h]
    exact CFSG.pCore_isPGroup
  have hEf : E ≤ f.range := by
    intro g hg
    obtain ⟨l, hl⟩ := d.ε_surj ⟨g, hE hg⟩
    exact ⟨l, congrArg Subtype.val hl⟩
  obtain ⟨S, hSa, hSc, hSm⟩ := exists_elemAbelian_lift_of_ker f hker hp hp2 hEa hEf
  refine ⟨S.map L.subtype, ?_, IsElemAbelian.map hSa _, ?_⟩
  · intro x hx
    obtain ⟨s, hsS, rfl⟩ := Subgroup.mem_map.mp hx
    have hsL : (s : G) ∈ L := s.2
    refine ⟨hLM hsL, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    have hfs : f s ∈ E := hSm ▸ Subgroup.mem_map_of_mem f hsS
    have hfix' := hfix (f s) hfs
    have hv' : (s : G) * v * (s : G)⁻¹ ∈ V :=
      (mem_normalizer_iff.mp (hMV (hLM hsL)) v).mp hv
    have heq := d.equiv s ⟨v, hv⟩ ⟨_, hv'⟩ rfl
    have h1 : d.φ ⟨_, hv'⟩ = d.φ ⟨v, hv⟩ := by
      rw [heq]
      have e : ((d.ε s : ↥(StatedOmega (StatedQuadMinus 3 d.F d.b d.c))) :
          GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) = f s := rfl
      rw [e, hfix', ofAdd_toAdd]
    have h2 : (⟨(s : G) * v * (s : G)⁻¹, hv'⟩ : ↥V) = ⟨v, hv⟩ := d.φ_bij.1 h1
    have h3 : (s : G) * v * (s : G)⁻¹ = v := congrArg Subtype.val h2
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    calc v * (s : G) = ((s : G) * v * (s : G)⁻¹) * (s : G) := by rw [h3]
      _ = (s : G) * v := by group
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hSc, hk]

theorem O6NatData.exists_lift_stab {n p : ℕ} {M L V : Subgroup G} [Finite G]
    (d : O6NatData G n L V) (hp : p.Prime) (hp2 : p ≠ 2) (hLM : L ≤ M)
    (hMV : M ≤ normalizer (V : Set G)) (W' : Subgroup G)
    (Y₀ : Set (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F))
    (hW' : ∀ v : ↥V, (v : G) ∈ W' ↔ Multiplicative.toAdd (d.φ v) ∈ Y₀)
    (hW'V : W' ≤ V) {k : ℕ}
    (E : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F))
    (hE : E ≤ StatedOmega (StatedQuadMinus 3 d.F d.b d.c)) (hEa : IsElemAbelian p E)
    (hk : Nat.card E = p ^ k)
    (hEY : ∀ g ∈ E, ∀ x ∈ Y₀,
      ((g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) *ᵥ
        x ∈ Y₀) :
    ∃ S : Subgroup G, S ≤ M ⊓ normalizer (W' : Set G) ∧ IsElemAbelian p S ∧
      Nat.card S = p ^ k := by
  set f : ↥L →* GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F :=
    (StatedOmega (StatedQuadMinus 3 d.F d.b d.c)).subtype.comp d.ε with hf
  have hker : IsPGroup 2 ↥f.ker := by
    have h : f.ker = CFSG.pCore 2 ↥L := by
      rw [hf, MonoidHom.ker_comp_of_injective _ _
        (StatedOmega (StatedQuadMinus 3 d.F d.b d.c)).subtype_injective, d.ε_ker]
    rw [h]
    exact CFSG.pCore_isPGroup
  have hEf : E ≤ f.range := by
    intro g hg
    obtain ⟨l, hl⟩ := d.ε_surj ⟨g, hE hg⟩
    exact ⟨l, congrArg Subtype.val hl⟩
  obtain ⟨S, hSa, hSc, hSm⟩ := exists_elemAbelian_lift_of_ker f hker hp hp2 hEa hEf
  have key : ∀ u : ↥L, f u ∈ E → ∀ x ∈ W', (u : G) * x * (u : G)⁻¹ ∈ W' := by
    intro u hu x hx
    have hxV : x ∈ V := hW'V hx
    have hcV : (u : G) * x * (u : G)⁻¹ ∈ V :=
      (mem_normalizer_iff.mp (hMV (hLM u.2)) x).mp hxV
    have hequiv := d.equiv u ⟨x, hxV⟩ ⟨(u : G) * x * (u : G)⁻¹, hcV⟩ rfl
    refine (hW' ⟨(u : G) * x * (u : G)⁻¹, hcV⟩).mpr ?_
    rw [hequiv, toAdd_ofAdd]
    exact hEY (f u) hu _ ((hW' ⟨x, hxV⟩).mp hx)
  refine ⟨S.map L.subtype, ?_, IsElemAbelian.map hSa _, ?_⟩
  · intro s hs
    obtain ⟨t, htS, rfl⟩ := Subgroup.mem_map.mp hs
    have hft : f t ∈ E := hSm ▸ Subgroup.mem_map_of_mem f htS
    have hft' : f t⁻¹ ∈ E := by
      rw [map_inv]
      exact E.inv_mem hft
    have hN : L.subtype t ∈ normalizer (W' : Set G) := by
      rw [mem_normalizer_iff]
      intro h
      refine ⟨key t hft h, fun hh => ?_⟩
      have h2 := key t⁻¹ hft' ((t : G) * h * (t : G)⁻¹) hh
      have h3 : ((t⁻¹ : ↥L) : G) * ((t : G) * h * (t : G)⁻¹) * ((t⁻¹ : ↥L) : G)⁻¹ = h := by
        simp only [Subgroup.coe_inv]
        group
      rw [← h3]
      exact h2
    exact ⟨hLM t.2, hN⟩
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hSc, hk]

end CFSG.LocalAnalysis.RankThreeUC
