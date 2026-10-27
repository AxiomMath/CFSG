module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcLOuterCheck
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporAut
public import CFSG.Sporadic.SmallOddCore.McLAut
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporLocal
public import CFSG.Sporadic.SmallOddCore.McLLocal

public noncomputable section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.Sporadic.SuzOddCore CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore.Native CFSG.ComponentClassification.OuterAutomorphisms

abbrev mclU1 : Equiv.Perm (Fin 275) := tp 275 (mclCentTbl 17)

abbrev mclC1 : Subgroup (Equiv.Perm (Fin 275)) := mclP ⊓ centralizer ({mclU1} : Set _)

theorem mclU1_facts : mclU1 ∈ mclR ∧ mclU1 ∉ mclP ∧ orderOf mclU1 = 2 ∧
    closure (tp 275 '' {x | x ∈ [mclCentTbl 18, mclCentTbl 19, mclCentTbl 20,
      mclCentTbl 21].toArray}) = mclC1 ∧ Nat.card mclC1 = 7920 := by
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ := mcl_involution_centralizers
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hrows _ (List.mem_cons_of_mem _ List.mem_cons_self)
  dsimp only [CFSG.Sporadic.SmallOddCore.mclC] at h1 h2 h3 h4 h5
  exact ⟨h1, h3.1 rfl, h2, h4, h5⟩

theorem rep_mclU1 : CFSG.Monster.B.Co2.Rep 275 mclU1Arr mclU1 :=
  co2Rep_natArr_iff.2 (rep_tp mclY_basic.2.2.2.2.1)

theorem mem_mclFix1 (x : Fin 275) : (x : ℕ) ∈ mclFix1 ↔ mclU1 x = x := by
  rw [mclFix1, fixedList, List.mem_filter, List.mem_range, beq_iff_eq, rep_mclU1 x]
  exact ⟨fun h => Fin.ext h.2, fun h => ⟨x.2, by rw [h]⟩⟩

theorem mclFix1_points : PointsList 275 11 mclFix1 where
  len := mclY_basic.1
  lt x hx := by
    rw [mclFix1, fixedList, List.mem_filter, List.mem_range] at hx
    exact hx.1
  nodup := List.nodup_range.filter _

theorem mclC1_preserves :
    ∀ g ∈ mclC1, ∀ x : Fin 275, (x : ℕ) ∈ mclFix1 → (g x : ℕ) ∈ mclFix1 := by
  intro g hg x hx
  rw [mem_mclFix1] at hx ⊢
  have key : ∀ u : Equiv.Perm (Fin 275), g ∈ centralizer ({u} : Set _) → u x = x → u (g x) = g x := by
    intro u hu hux
    have hc := mem_centralizer_singleton_iff.1 hu
    have := congrArg (fun σ : Equiv.Perm (Fin 275) => σ x) hc
    simp only [Equiv.Perm.mul_apply, hux] at this
    exact this.symm
  exact key _ (mem_inf.1 hg).2 hx

@[expose] def mclRho1 : mclC1 →* Equiv.Perm (Fin 11) :=
  mclFix1_points.restrHom mclC1 mclC1_preserves

theorem mclC1Gen_mem {k : ℕ} (hk : k < 4) : tp 275 (mclCentTbl (k + 18)) ∈ mclC1 := by
  rw [← mclU1_facts.2.2.2.1]
  refine subset_closure ⟨mclCentTbl (k + 18), ?_, rfl⟩
  interval_cases k <;> simp

@[expose] def mclC1Gen (k : ℕ) : mclC1 :=
  if hk : k < 4 then ⟨tp 275 (mclCentTbl (k + 18)), mclC1Gen_mem hk⟩ else 1

@[expose] def mclYPerm (k : ℕ) : Equiv.Perm (Fin 11) := mclRho1 (mclC1Gen k)

theorem tabRep_mclYGens : ∀ k < mclYGens.size, TabRep mclYGens[k]! (mclYPerm k) := by
  intro k hk
  have hk4 : k < 4 := by simpa [mclYGens] using hk
  have h1 : mclYGens[k]! = restrictArr mclFix1 (natArr (mclCentTbl (k + 18))) := by
    rw [mclYGens, getElem!_pos _ k (by simpa using hk4), Array.getElem_ofFn]
  rw [h1, mclYPerm]
  refine mclFix1_points.tabRep_restrHom _ _ _ ?_
  simp only [mclC1Gen, hk4, ↓reduceDIte]
  exact co2Rep_natArr_iff.2 (rep_tp (mclY_basic.2.2.2.2.2 k hk4))

theorem mclY_cert :
    ClassCert 11 mclYGens mclYInvs mclYEnum 10 mclYWords mclYSizes mclYOrbits where
  enum := mclY_enum.1
  words_lt := mclY_orbits.2.2.1
  rep0 := mclY_orbits.2.2.2
  orbit := mclY_orbits.1
  notIn := mclY_orbits.2.1
  cover := by
    intro k hk
    obtain ⟨l, hl, hf⟩ := cover_of_coverAllOK mclY_cover k hk
    exact ⟨l, by rw [mclY_basic.2.2.2.1] at hl; exact hl, hf⟩

theorem mclY_simple : IsSimpleGroup (genGroup 11 mclYGens mclYPerm) ∧
    ∃ a b : genGroup 11 mclYGens mclYPerm, a * b ≠ b * a :=
  isSimpleGroup_of_classCert tabRep_mclYGens mclY_cert (by norm_num)
    (by rw [mclY_enum.2]; norm_num) (by rw [mclY_enum.2]; exact mclY_sums) ⟨1, by decide⟩

theorem card_mclY : Nat.card (genGroup 11 mclYGens mclYPerm) = 7920 := by
  rw [(genGroup_enumerates tabRep_mclYGens mclY_cert).card, Array.length_toList, mclY_enum.2]

theorem mclY_le_range : genGroup 11 mclYGens mclYPerm ≤ mclRho1.range := by
  rw [genGroup, closure_le]
  rintro _ ⟨k, -, rfl⟩
  exact ⟨mclC1Gen k, rfl⟩

theorem mclC1_simple : IsSimpleGroup mclC1 ∧ (∃ a b : mclC1, a * b ≠ b * a) ∧
    Nat.card mclC1 = 7920 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup mclRho1.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange mclRho1).toEquiv,
    mclU1_facts.2.2.2.2] at h
  have hle := Subgroup.card_le_of_le mclY_le_range
  rw [card_mclY] at hle
  have hpos : 0 < Nat.card mclRho1.ker := Nat.card_pos
  have hrange : Nat.card mclRho1.range = 7920 := by
    have h1 : Nat.card mclRho1.range ≤ 7920 := by
      have := Nat.le_mul_of_pos_right (Nat.card mclRho1.range) hpos
      omega
    omega
  have hker : Nat.card mclRho1.ker = 1 := by
    rw [hrange] at h
    omega
  have hinj : Function.Injective mclRho1 := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact Subgroup.eq_bot_of_card_eq _ hker
  have hreq : mclRho1.range = genGroup 11 mclYGens mclYPerm :=
    (Subgroup.eq_of_le_of_card_ge mclY_le_range (by rw [hrange, card_mclY])).symm
  let e : mclC1 ≃* genGroup 11 mclYGens mclYPerm :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hreq)
  obtain ⟨hs, a, b, hab⟩ := mclY_simple
  refine ⟨e.isSimpleGroup, ⟨e.symm a, e.symm b, fun h => hab ?_⟩, mclU1_facts.2.2.2.2⟩
  have := congrArg e h
  simpa only [map_mul, MulEquiv.apply_symm_apply] using this

theorem mcl_outer_comps {G : Type} [Group G] (e : G ≃* NativeSporadic.McL) (α : MulAut G)
    (hα2 : α * α = 1) (hα : α ∉ inner G) :
    CompsSatisfy (fixSub α) fun Y _ => Nat.card (Y ⧸ center Y) ∈ ({7920} : Set ℕ) := by
  set θ : G ≃* mclP := e.trans mclPermEquiv
  set β : MulAut mclP := transportAut θ α
  have hβ2 : β * β = 1 := transportAut_mul_self θ hα2
  have hβ : β ∉ inner mclP := transportAut_not_mem_inner θ hα
  obtain ⟨x, hxR, hx⟩ := mcl_autModel.surj β
  have hxP : x ∉ mclP := by
    intro hxP
    apply hβ
    refine ⟨⟨x, hxP⟩, MulEquiv.ext fun p => Subtype.ext ?_⟩
    rw [hx p]
    rfl
  have hx2 : x * x = 1 := by
    apply mcl_autModel.inj (x * x) (mclR.mul_mem hxR hxR)
    intro p hp
    have h := congrArg (fun φ : MulAut mclP => ((φ ⟨p, hp⟩ : mclP) : Equiv.Perm (Fin 275))) hβ2
    simp only [MulAut.mul_apply, MulAut.one_apply] at h
    rw [hx, hx] at h
    calc x * x * p = x * (x * p * x⁻¹) * x⁻¹ * (x * x) := by group
      _ = p * (x * x) := by rw [h]
  have hx1 : x ≠ 1 := fun h1 => hxP (h1 ▸ one_mem _)
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  obtain ⟨-, -, -, -, hcover, -, -, -⟩ := mcl_involution_centralizers
  obtain ⟨r, hr, g, hg, hxg⟩ := hcover x hxR hxo
  simp only [mclRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  have hxu : x = g * mclU1 * g⁻¹ := by
    rcases hr with rfl | rfl
    · exfalso
      dsimp only at hxg
      apply hxP
      rw [hxg]
      exact mclP.mul_mem (mclP.mul_mem hg mclT0_facts.1) (mclP.inv_mem hg)
    · dsimp only at hxg
      exact hxg
  have hfix := map_fixSub_conjOn mclP β x hx
  rw [hxu, centralizerIn_conj mclP hg] at hfix
  have eC : ↥(fixSub α) ≃* ↥mclC1 :=
    ((fixSubTransportEquiv θ α).trans ((((fixSub β).equivMapOfInjective mclP.subtype
      mclP.subtype_injective).trans (MulEquiv.subgroupCongr hfix)))).trans
        (conjEquiv mclC1 g).symm
  obtain ⟨hs, hnab, hcard⟩ := mclC1_simple
  refine CompsSatisfy.of_mulEquiv (isoInvariant_card_quotient_center _) eC ?_
  rw [← hcard]
  exact compsSatisfy_of_isSimpleGroup hnab

end CFSG.ComponentClassification.RestrictedStd.Spor
