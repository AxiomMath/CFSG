module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcCompCenterQHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ClassicalReduce
import CFSG.GroupTheory.PLayer.CentralQuotient

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

section Transport

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem s2019Omega_of_excComp {p : ℕ} (hp : p.Prime) {S B D J : Subgroup Ω} [hSn : S.Normal]
    (hSp : GLAPPrimeCore p ↥S = ⊥) (hBel : IsElemAbelian p B) {G : Type} [Group G]
    (e : ↥S ⧸ Subgroup.center ↥S ≃* G)
    (hfix : ∀ b ∈ D, b ∈ B → b ∉ centModSubgroup p S → ∀ L : Subgroup G,
      GLAPComponent p (fixSubgroup (transAut e b)) L →
      (∃ A : Subgroup (MulAut (↥L ⧸ Subgroup.center ↥L)), IsElemAbelian p A ∧
        p ^ 2 ≤ Nat.card A) →
      ∀ T : Subgroup G, IsPGroup 2 T → L ≤ Subgroup.normalizer (T : Set G) → ⁅T, L⁆ = ⊥) :
    S2019Omega p S B D J := by
  classical
  intro _ hDB hCD hrel hD hJ hBJ hcm T hTS hT2 hJT
  have hJperf : ⁅J, J⁆ = J := glaPComponent_perfect hJ
  have hJS : J ≤ S := hJ.1.trans inf_le_left
  obtain ⟨b, hbD, hbC⟩ : ∃ b ∈ D, b ∉ B ⊓ centModSubgroup p S := by
    by_contra hcon
    push Not at hcon
    have h1 : (B ⊓ centModSubgroup p S).relIndex D = 1 := Subgroup.relIndex_eq_one.2 hcon
    rw [hrel] at h1
    exact hp.one_lt.ne' h1
  have hbB : b ∈ B := hDB hbD
  have hbC' : b ∉ centModSubgroup p S := fun h => hbC ⟨hbB, h⟩
  have hXeq : S ⊓ Subgroup.centralizer (D : Set Ω) = S ⊓ Subgroup.centralizer ({b} : Set Ω) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hbD))
    · intro s hs'
      obtain ⟨hs, hsb⟩ := Subgroup.mem_inf.1 hs'
      refine Subgroup.mem_inf.2 ⟨hs, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hsb
      have hDs := le_centralizer_of_commute hp hSp hCD hrel hbD hbC hs hsb
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact Subgroup.mem_centralizer_singleton_iff.1 (hDs hd)
  rw [hXeq] at hJ
  set α : MulAut ↥S := MulAut.conjNormal b with hα
  have hfixα : (fixSubgroup α).map S.subtype = S ⊓ Subgroup.centralizer ({b} : Set Ω) := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine Subgroup.mem_inf.2 ⟨s.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : ((α s : ↥S) : Ω) = s := congrArg Subtype.val hs
      rw [hα, MulAut.conjNormal_apply] at h1
      calc (s : Ω) * b = b * s * b⁻¹ * b := by rw [h1]
        _ = b * s := by group
    · intro hx
      obtain ⟨hxS, hxb⟩ := Subgroup.mem_inf.1 hx
      refine Subgroup.mem_map.2 ⟨⟨x, hxS⟩, ?_, rfl⟩
      rw [mem_fixSubgroup]
      apply Subtype.ext
      rw [hα, MulAut.conjNormal_apply]
      rw [Subgroup.mem_centralizer_singleton_iff] at hxb
      calc b * x * b⁻¹ = x * b * b⁻¹ := by rw [hxb]
        _ = x := by group
  have hsub : ∀ y ∈ fixSubgroup α ⊓ S.subtype.ker, ∀ x ∈ fixSubgroup α, x * y = y * x := by
    intro y hy x _
    have hy' := (Subgroup.mem_inf.1 hy).2
    rw [Subgroup.ker_subtype, Subgroup.mem_bot] at hy'
    rw [hy', mul_one, one_mul]
  rw [← hfixα] at hJ
  obtain ⟨J₀, hJ₀, hJ₀J⟩ := (CFSG.glaPComponent_map_bijective_of_ker_le_center hp S.subtype
    hsub).2 J hJ
  set T₀ : Subgroup ↥S := T.subgroupOf S with hT₀
  have hT₀T : T₀.map S.subtype = T := by
    rw [hT₀, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hTS]
  have hJ₀N : J₀ ≤ Subgroup.normalizer (T₀ : Set ↥S) := by
    intro j hj
    have hjJ : (j : Ω) ∈ J := by
      rw [← hJ₀J]
      exact Subgroup.mem_map_of_mem _ hj
    have hjN := hJT hjJ
    rw [Subgroup.mem_normalizer_iff] at hjN ⊢
    intro t
    rw [hT₀, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using hjN (t : Ω)
  set ψ : ↥S →* ↥S ⧸ Subgroup.center ↥S := QuotientGroup.mk' (Subgroup.center ↥S) with hψ
  have hψs : Function.Surjective ψ := QuotientGroup.mk'_surjective _
  have hψk : ψ.ker ≤ Subgroup.center ↥S := (QuotientGroup.ker_mk' _).le
  have hαβ : ∀ k, ψ (α k) = actQuot S b (ψ k) := fun k => (actQuot_mk S b k).symm
  have hJ₁ := CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_map_fixSubgroup ψ hψk α
    (actQuot S b) hαβ hψs hp hJ₀
  have hsubG : ∀ y ∈ fixSubgroup (actQuot S b) ⊓ e.toMonoidHom.ker,
      ∀ x ∈ fixSubgroup (actQuot S b), x * y = y * x := by
    intro y hy x _
    have hy1 : y = 1 := e.injective (by rw [map_one]; exact (Subgroup.mem_inf.1 hy).2)
    rw [hy1, mul_one, one_mul]
  haveI : Finite G := Finite.of_equiv _ e.toEquiv
  have hJ₂ := (CFSG.glaPComponent_map_bijective_of_ker_le_center hp e.toMonoidHom hsubG).1 _ hJ₁
  rw [← fixSubgroup_transAut] at hJ₂
  have hT₂ : IsPGroup 2 ((T₀.map ψ).map e.toMonoidHom) := by
    have hT₀2 : IsPGroup 2 T₀ := fun t => by
      have htT : ((t : ↥S) : Ω) ∈ T := Subgroup.mem_subgroupOf.1 t.2
      obtain ⟨k, hk⟩ := hT2 ⟨((t : ↥S) : Ω), htT⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg Subtype.val hk
      simpa using this
    exact (hT₀2.map ψ).map e.toMonoidHom
  have hN₂ : (J₀.map ψ).map e.toMonoidHom ≤
      Subgroup.normalizer (((T₀.map ψ).map e.toMonoidHom : Subgroup G) : Set G) := by
    refine (Subgroup.map_mono (Subgroup.map_mono hJ₀N |>.trans
      (Subgroup.le_normalizer_map ψ))).trans (Subgroup.le_normalizer_map _)
  set L : Subgroup G := (J₀.map ψ).map e.toMonoidHom with hL
  haveI : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.2 hJperf
  let θ : ↥B →* MulAut (↥J ⧸ Subgroup.center ↥J) :=
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥J).comp
      ((Subgroup.normalizerMonoidHom J).comp (Subgroup.inclusion hBJ))
  have hθker : ∀ x : ↥B, θ x = 1 → (x : Ω) ∈ D := by
    intro x hx
    have h1 : Subgroup.normalizerMonoidHom J (Subgroup.inclusion hBJ x) = 1 :=
      CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective ↥J
        (hx.trans (map_one _).symm)
    have hxJ : ∀ j ∈ J, (x : Ω) * j = j * x := by
      intro j hj
      have h2 := congrArg (fun φ : MulAut ↥J => ((φ ⟨j, hj⟩ : ↥J) : Ω)) h1
      simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion,
        MulAut.one_apply] at h2
      calc (x : Ω) * j = ((x : Ω) * j * (x : Ω)⁻¹) * x := by group
        _ = j * x := by rw [h2]
    refine (hcm x x.2).1 ⟨hBJ x.2, ?_⟩
    have hbot : ⁅J, Subgroup.zpowers (x : Ω)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro j hj
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact ((Commute.zpow_left (hxJ j hj) k)).eq
    rw [hbot]
    exact bot_le
  have hθcard : p ^ 2 ≤ Nat.card θ.range := by
    have hsplit : Nat.card ↥B = Nat.card θ.range * Nat.card θ.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker]
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv]
    have hkerD : Nat.card θ.ker ≤ Nat.card D := by
      refine Nat.card_le_card_of_injective
        (fun x => (⟨((x : ↥B) : Ω), hθker x (MonoidHom.mem_ker.1 x.2)⟩ : D)) ?_
      intro a c h
      have h' : ((a : ↥B) : Ω) = ((c : ↥B) : Ω) := congrArg (fun d : ↥D => (d : Ω)) h
      exact Subtype.ext (Subtype.ext h')
    have hDpos : 0 < Nat.card D := Nat.card_pos
    have h3 : p ^ 2 * Nat.card D ≤ Nat.card θ.range * Nat.card D :=
      calc p ^ 2 * Nat.card D ≤ Nat.card ↥B := hD
        _ = Nat.card θ.range * Nat.card θ.ker := hsplit
        _ ≤ Nat.card θ.range * Nat.card D := Nat.mul_le_mul_left _ hkerD
    exact Nat.le_of_mul_le_mul_right h3 hDpos
  have hθel : IsElemAbelian p θ.range := by
    have h1 : IsElemAbelian p (⊤ : Subgroup ↥B) :=
      ⟨⟨⟨fun a c => Subtype.ext (hBel.1.is_comm.comm (a : ↥B) (c : ↥B))⟩⟩,
        fun x _ => Subtype.ext (by simpa using hBel.2 x x.2)⟩
    rw [MonoidHom.range_eq_map]
    exact CFSG.SectionRank.isElemAbelian_map h1 θ
  have hmemL : ∀ j : ↥J, e (ψ (Subgroup.inclusion hJS j)) ∈ L := by
    intro j
    have hj : (j : Ω) ∈ J₀.map S.subtype := by rw [hJ₀J]; exact j.2
    obtain ⟨j₀, hj₀, hj₀j⟩ := hj
    have : Subgroup.inclusion hJS j = j₀ := Subtype.ext hj₀j.symm
    rw [this]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hj₀)
  let f : ↥J →* ↥L :=
    ((e.toMonoidHom.comp ψ).comp (Subgroup.inclusion hJS)).codRestrict L hmemL
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨z, ⟨j₀, hj₀, rfl⟩, rfl⟩ := hy
    have hj : ((j₀ : ↥S) : Ω) ∈ J := by
      rw [← hJ₀J]
      exact Subgroup.mem_map_of_mem _ hj₀
    exact ⟨⟨_, hj⟩, Subtype.ext rfl⟩
  have hfk : f.ker ≤ Subgroup.center ↥J := by
    intro j hj
    have h1 : e (ψ (Subgroup.inclusion hJS j)) = 1 := congrArg Subtype.val hj
    have h2 : Subgroup.inclusion hJS j ∈ Subgroup.center ↥S :=
      hψk ((MulEquiv.map_eq_one_iff e).1 h1)
    rw [Subgroup.mem_center_iff]
    intro g
    have h3 := Subgroup.mem_center_iff.1 h2 (Subgroup.inclusion hJS g)
    have h4 : ((Subgroup.inclusion hJS g * Subgroup.inclusion hJS j : ↥S) : Ω) =
        ((Subgroup.inclusion hJS j * Subgroup.inclusion hJS g : ↥S) : Ω) := congrArg Subtype.val h3
    exact Subtype.ext h4
  obtain ⟨eJL⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
    (Group.isPerfect_def.1 inferInstance) f hf hfk
  set A : Subgroup (MulAut (↥L ⧸ Subgroup.center ↥L)) :=
    θ.range.map (MulAut.congr eJL).toMonoidHom with hA
  have hAel : IsElemAbelian p A := CFSG.SectionRank.isElemAbelian_map hθel _
  have hAcard : p ^ 2 ≤ Nat.card A := by
    rw [hA, Subgroup.card_map_of_injective (MulAut.congr eJL).injective]
    exact hθcard
  have hcomm := hfix b hbD hbB hbC' L hJ₂ ⟨A, hAel, hAcard⟩ _ hT₂ hN₂
  rw [hL, ← Subgroup.map_commutator, ← Subgroup.map_commutator,
    Subgroup.map_eq_bot_iff_of_injective _ e.injective, Subgroup.map_eq_bot_iff] at hcomm
  have hTJ₀ : ⁅T₀, J₀⁆ ≤ Subgroup.center ↥S := hcomm.trans hψk
  have hJ₀perf : ⁅J₀, J₀⁆ = J₀ := glaPComponent_perfect hJ₀
  have h0 := commutator_eq_bot_of_le_center hJ₀perf hTJ₀
  rw [← hT₀T, ← hJ₀J, ← Subgroup.map_commutator, h0, Subgroup.map_bot]

end Transport

section Holds


theorem s2019FactExceptionalLie_holds (hsec : S2019ExcSecRank) (hree : S2019ExcCompNotRee) :
    S2019FactExceptionalLie := by
  intro p q hp hp2 hq hq2 hqp Ω _ _ S B D J hSn hSq hSp hcat hBel hSB hrank
  haveI := hSn
  obtain ⟨i, hi, ⟨e₀⟩⟩ := hcat
  let e : ↥S ⧸ Subgroup.center ↥S ≃* i.Group := (pSimpleEquivQuotCenter hSp).symm.trans e₀
  haveI : Finite i.Group := Finite.of_equiv _ e.toEquiv
  haveI hSs : IsSimpleGroup (↥S ⧸ Subgroup.center ↥S) := hSq.2
  haveI : IsSimpleGroup i.Group := e.symm.isSimpleGroup
  have hSperf : ⁅S, S⁆ = S := commutator_self_eq_of_isQuasisimple hSq
  have hna : ∃ a b : i.Group, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hab : ∀ a b : ↥S ⧸ Subgroup.center ↥S, a * b = b * a := fun a b =>
      e.injective (by rw [map_mul, map_mul, hcon])
    have hle : commutator ↥S ≤ Subgroup.center ↥S := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
        hab (x : ↥S ⧸ Subgroup.center ↥S)]
      group
    rw [hSq.1] at hle
    have hsub : Subsingleton (↥S ⧸ Subgroup.center ↥S) := by
      refine ⟨fun a b => ?_⟩
      induction a using QuotientGroup.induction_on with | H a => ?_
      induction b using QuotientGroup.induction_on with | H b => ?_
      exact QuotientGroup.eq.2 (hle (Subgroup.mem_top _))
    obtain ⟨a, b, hab'⟩ :=
      (IsSimpleGroup.toNontrivial (G := ↥S ⧸ Subgroup.center ↥S)).exists_pair_ne
    exact hab' (Subsingleton.elim a b)
  have hK : catalogIs i.Group (onLie fun d => d.characteristic = q ∧ S2019ExcCoreIdx d) :=
    ⟨i, hi, ⟨MulEquiv.refl _⟩⟩
  refine s2019Omega_of_excComp hp hSp hBel e ?_
  intro b _ hbB hbC L hL hA T hT hLT
  have hβp : transAut e b ^ p = 1 := transAut_pow_eq_one e (hBel.2 b hbB)
  have hβ1 : transAut e b ≠ 1 := by
    intro h1
    have hact : actQuot S b = 1 := by
      ext y
      have h2 := congrArg (fun φ : MulAut i.Group => φ (e y)) h1
      change e (actQuot S b (e.symm (e y))) = e y at h2
      rw [MulEquiv.symm_apply_apply] at h2
      rw [MulAut.one_apply]
      exact e.injective h2
    have hcen : b ∈ Subgroup.centralizer (S : Set Ω) := by
      refine le_centralizer_of_actQuot_eq_one S hSperf (K := Subgroup.zpowers b) ?_
        (Subgroup.mem_zpowers _)
      intro k hk
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
      rw [map_zpow, hact, one_zpow]
    refine hbC ⟨?_, fun l hl => ?_⟩
    · rw [Subgroup.normalizer_eq_top_iff.2 hSn]
      exact Subgroup.mem_top _
    · rw [glaPPrimeCoreOf_eq_bot hSp, Subgroup.mem_bot, commutatorElement_def]
      have h1 : l * b = b * l := Subgroup.mem_centralizer_iff.1 hcen l hl
      rw [h1]
      group
  exact commutator_eq_bot_of_excComp hsec s2019ExcCompCenterQ_holds hree hp hp2 hq hq2 hqp hK
    inferInstance hna hβp hβ1 hL hA hT hLT

end Holds

end CFSG.LocalAnalysis.GLTheoremA.S2019
