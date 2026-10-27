module

public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

@[expose] def i269Fix {S : Type} [Group S] (E : Subgroup (MulAut S)) : Subgroup S :=
  ⨅ (α : MulAut S) (_ : α ∈ E), fixSubgroup α

theorem mem_i269Fix {S : Type} [Group S] {E : Subgroup (MulAut S)} {x : S} :
    x ∈ i269Fix E ↔ ∀ α ∈ E, α x = x := by
  simp only [i269Fix, Subgroup.mem_iInf, mem_fixSubgroup]

@[expose] def E9Solv (S : Type) [Group S] : Prop :=
  ∀ E : Subgroup (MulAut S), IsElemAbelian 3 E → Nat.card E = 9 →
    Group.IsSolvable ↥(i269Fix E)

section Transport

theorem i269Fix_map {S T : Type} [Group S] [Group T] (e : S ≃* T) (E : Subgroup (MulAut S)) :
    i269Fix (E.map (MulAut.congr e).toMonoidHom) = (i269Fix E).map e.toMonoidHom := by
  ext y
  rw [mem_i269Fix, Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [mem_i269Fix]
    intro α hα
    apply e.injective
    have := h ((MulAut.congr e) α) (Subgroup.mem_map_of_mem _ hα)
    simpa [MulAut.congr] using this
  · rintro ⟨x, hx, rfl⟩ β hβ
    obtain ⟨α, hα, rfl⟩ := Subgroup.mem_map.1 hβ
    have := (mem_i269Fix.1 hx) α hα
    simp [MulAut.congr, this]

theorem isSolvable_of_mulEquiv' {H K : Type} [Group H] [Group K] (f : H ≃* K)
    [Group.IsSolvable K] : Group.IsSolvable H :=
  Group.isSolvable_of_surjective (f := f.symm.toMonoidHom) f.symm.surjective

theorem E9Solv.of_mulEquiv {S T : Type} [Group S] [Group T] (hT : E9Solv T) (e : S ≃* T) :
    E9Solv S := by
  intro E hE hcard
  have hinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  have hE' : IsElemAbelian 3 (E.map (MulAut.congr e).toMonoidHom) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨α, hα, hαa⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨β, hβ, hβb⟩ := Subgroup.mem_map.1 b.2
      have hc : α * β = β * α := congrArg Subtype.val (hE.1.is_comm.comm ⟨α, hα⟩ ⟨β, hβ⟩)
      apply Subtype.ext
      show (a : MulAut T) * (b : MulAut T) = (b : MulAut T) * (a : MulAut T)
      rw [← hαa, ← hβb, ← map_mul, ← map_mul, hc]
    · rintro _ ⟨α, hα, rfl⟩
      show (MulAut.congr e α) ^ 3 = 1
      rw [← map_pow, hE.2 α hα, map_one]
  have hcard' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective hinj, hcard]
  have hs := hT _ hE' hcard'
  rw [i269Fix_map] at hs
  haveI := hs
  exact isSolvable_of_mulEquiv' (Subgroup.equivMapOfInjective (i269Fix E) e.toMonoidHom e.injective)

end Transport

section Solvable

theorem isSolvable_of_le_isSolvable {S : Type} [Group S] {H K : Subgroup S} (hHK : H ≤ K)
    [Group.IsSolvable ↥K] : Group.IsSolvable ↥H :=
  isSolvable_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hHK).symm

theorem isSolvable_of_factor {A B C : Type} [Group A] [Group B] [Group C] (f : A →* B)
    (g : A →* C) (hg : Function.Surjective g) (hker : f.ker ≤ g.ker)
    [Group.IsSolvable ↥f.range] : Group.IsSolvable C := by
  let θ : A →* ↥f.range := f.rangeRestrict
  have hθ : Function.Surjective θ := MonoidHom.rangeRestrict_surjective f
  have hkθ : θ.ker = f.ker := MonoidHom.ker_rangeRestrict f
  let lift : A ⧸ θ.ker →* C := QuotientGroup.lift θ.ker g (by rw [hkθ]; exact hker)
  have hlift : Function.Surjective lift := by
    intro c
    obtain ⟨a, rfl⟩ := hg c
    exact ⟨(a : A ⧸ θ.ker), rfl⟩
  let ψ : ↥f.range →* C := lift.comp (QuotientGroup.quotientKerEquivOfSurjective θ hθ).symm.toMonoidHom
  have hψ : Function.Surjective ψ := hlift.comp (QuotientGroup.quotientKerEquivOfSurjective θ hθ).symm.surjective
  exact Group.isSolvable_of_surjective hψ

theorem not_isSolvable_quasisimple_mod_center (Q : Type) [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q) : ¬ Group.IsSolvable (Q ⧸ Subgroup.center Q) := by
  intro hsol
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  have hcomm : ∀ a b : Q ⧸ Subgroup.center Q, a * b = b * a :=
    (IsSimpleGroup.comm_iff_isSolvable).2 hsol
  have hbot : commutator (Q ⧸ Subgroup.center Q) = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a _
    rw [Subgroup.mem_centralizer_iff]
    intro h _
    exact hcomm h a
  have htop : commutator (Q ⧸ Subgroup.center Q) = ⊤ := by
    have hq : commutator Q = ⊤ := hQ.1
    calc commutator (Q ⧸ Subgroup.center Q)
        = (commutator Q).map (QuotientGroup.mk' (Subgroup.center Q)) := by
          unfold commutator
          rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
      _ = ⊤ := by rw [hq, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hbt : (⊤ : Subgroup (Q ⧸ Subgroup.center Q)) = ⊥ := by rw [← htop, hbot]
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  have ha : a = 1 := by
    have hx : a ∈ (⊤ : Subgroup (Q ⧸ Subgroup.center Q)) := Subgroup.mem_top a
    rw [hbt] at hx
    exact Subgroup.mem_bot.1 hx
  have hb : b = 1 := by
    have hx : b ∈ (⊤ : Subgroup (Q ⧸ Subgroup.center Q)) := Subgroup.mem_top b
    rw [hbt] at hx
    exact Subgroup.mem_bot.1 hx
  exact hab (ha.trans hb.symm)

end Solvable

section Reduction

variable {G : Type} [Group G] [Finite G]

theorem chevAut_fix_chevQuotHom {L D : Subgroup G} (hDN : D ≤ Subgroup.normalizer (L : Set G))
    {d : G} (hd : d ∈ D) {x : G} (hx : x ∈ L) (hxC : x ∈ Subgroup.centralizer (D : Set G)) :
    chevAut 3 L ⟨d, hDN hd⟩ (chevQuotHom 3 L ⟨x, hx⟩) = chevQuotHom 3 L ⟨x, hx⟩ := by
  rw [chevAut_chevQuotHom]
  congr 1
  apply Subtype.ext
  rw [chev_coe_normalizerMonoidHom]
  have hc : d * x = x * d := Subgroup.mem_centralizer_iff.1 hxC d hd
  show d * x * d⁻¹ = x
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]

theorem commutator_mem_of_chevQuotHom_eq_one {L : Subgroup G} {x : G} (hx : x ∈ L)
    (h1 : chevQuotHom 3 L ⟨x, hx⟩ = 1) {y : G} (hy : y ∈ L) :
    (y * x)⁻¹ * (x * y) ∈ GLAPPrimeCoreOf 3 L := by
  have hc : (QuotientGroup.mk (⟨x, hx⟩ : ↥L) : PQuot 3 L) ∈ Subgroup.center (PQuot 3 L) := by
    have h2 : (QuotientGroup.mk' (Subgroup.center (PQuot 3 L)))
        ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) (⟨x, hx⟩ : ↥L)) = 1 := h1
    exact QuotientGroup.eq_one_iff _ |>.1 h2
  have hcomm := Subgroup.mem_center_iff.1 hc (QuotientGroup.mk (⟨y, hy⟩ : ↥L))
  have key : (QuotientGroup.mk (⟨y, hy⟩ * ⟨x, hx⟩ : ↥L) : PQuot 3 L) =
      QuotientGroup.mk (⟨x, hx⟩ * ⟨y, hy⟩ : ↥L) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact hcomm
  exact (pQuot_mk_eq_mk_iff _ _).1 key

theorem mk_eq_of_mem_glaPPrimeCoreOf {Y : Subgroup G} {u v : G} (hu : u ∈ Y) (hv : v ∈ Y)
    (h : u⁻¹ * v ∈ GLAPPrimeCoreOf 3 Y) :
    (QuotientGroup.mk (⟨u, hu⟩ : ↥Y) : ↥Y ⧸ GLAPPrimeCore 3 ↥Y) = QuotientGroup.mk ⟨v, hv⟩ := by
  have hx : u⁻¹ * v ∈ Y := Y.mul_mem (Y.inv_mem hu) hv
  have h2 := (chev_mem_glaPPrimeCoreOf_iff hx).1 h
  rw [QuotientGroup.eq]
  convert h2 using 2

theorem layer_eq_bot_of_E9 {X L D : Subgroup G} (hL : GLAPComponent 3 X L)
    (hE : E9Solv (PSimple 3 L)) (hDN : D ≤ Subgroup.normalizer (L : Set G))
    (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 3 ^ 2 * Nat.card ↥(D ⊓ centModSubgroup 3 L)) :
    GLAPLayer 3 (L ⊓ Subgroup.centralizer (D : Set G)) = ⊥ := by
  classical
  let φ : ↥D →* MulAut (PSimple 3 L) := (chevAut 3 L).comp (Subgroup.inclusion hDN)
  have hφ : ∀ d : ↥D, φ d = chevAut 3 L ⟨d.1, hDN d.2⟩ := fun d => rfl
  have hker : ∀ d : ↥D, φ d = 1 ↔ d.1 ∈ centModSubgroup 3 L := by
    intro d
    rw [hφ, chevAut_eq_one_iff Nat.prime_three hL (hDN d.2), centMod_iff]
  have hEcard : Nat.card φ.range = 9 := by
    have hpos : 0 < Nat.card ↥(D ⊓ centModSubgroup 3 L) := Nat.card_pos
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    have h2 : Nat.card (↥D ⧸ φ.ker) = Nat.card φ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    have h3 : Nat.card φ.ker = Nat.card ↥(D ⊓ centModSubgroup 3 L) := by
      apply Nat.card_congr
      exact
        { toFun := fun x => ⟨x.1.1, Subgroup.mem_inf.2 ⟨x.1.2, (hker x.1).1 (MonoidHom.mem_ker.1 x.2)⟩⟩
          invFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩,
            MonoidHom.mem_ker.2 ((hker ⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩).2 (Subgroup.mem_inf.1 y.2).2)⟩
          left_inv := fun x => rfl
          right_inv := fun y => rfl }
    have hc : Nat.card D = Nat.card φ.range * Nat.card ↥(D ⊓ centModSubgroup 3 L) := by
      rw [← h3, ← h2]
      exact h1
    have h9 : Nat.card φ.range = 3 ^ 2 := Nat.eq_of_mul_eq_mul_right hpos (hc.symm.trans hcard)
    rw [h9]
    norm_num
  have hEel : IsElemAbelian 3 φ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨d, hd⟩ := MonoidHom.mem_range.1 a.2
      obtain ⟨e, he⟩ := MonoidHom.mem_range.1 b.2
      have hc : d * e = e * d := hD.1.is_comm.comm d e
      apply Subtype.ext
      show (a : MulAut (PSimple 3 L)) * (b : MulAut (PSimple 3 L)) =
        (b : MulAut (PSimple 3 L)) * (a : MulAut (PSimple 3 L))
      rw [← hd, ← he, ← map_mul, ← map_mul, hc]
    · rintro _ ⟨d, rfl⟩
      rw [← map_pow]
      have h3 : d ^ 3 = 1 := Subtype.ext (by simpa using hD.2 d.1 d.2)
      rw [h3, map_one]
  have hsolv : Group.IsSolvable ↥(i269Fix φ.range) := hE φ.range hEel hEcard
  haveI := hsolv
  set Y : Subgroup G := L ⊓ Subgroup.centralizer (D : Set G) with hYdef
  have hYL : Y ≤ L := inf_le_left
  have hYC : ∀ y ∈ Y, y ∈ Subgroup.centralizer (D : Set G) := fun y hy => (Subgroup.mem_inf.1 hy).2
  have key : ∀ J : Subgroup G, ¬ GLAPComponent 3 Y J := by
    intro J hJ
    have hJY : J ≤ Y := hJ.1
    have hJL : J ≤ L := hJY.trans hYL
    have hQq : CFSG.Open.IsQuasisimple
        ↥((J.subgroupOf Y).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y))) := hJ.2.2.1.2.2
    let ψ : ↥J →* ↥((J.subgroupOf Y).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y))) :=
      MonoidHom.codRestrict ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y)).comp (Subgroup.inclusion hJY))
        _ (fun x => Subgroup.mem_map.2 ⟨⟨x.1, hJY x.2⟩, Subgroup.mem_subgroupOf.2 x.2, rfl⟩)
    have hψsurj : Function.Surjective ψ := by
      intro q
      obtain ⟨y, hy, hyq⟩ := Subgroup.mem_map.1 q.2
      exact ⟨⟨y.1, Subgroup.mem_subgroupOf.1 hy⟩, Subtype.ext hyq⟩
    let F : ↥J →* (↥((J.subgroupOf Y).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y))) ⧸
        Subgroup.center ↥((J.subgroupOf Y).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y)))) :=
      (QuotientGroup.mk' _).comp ψ
    have hFsurj : Function.Surjective F := (QuotientGroup.mk'_surjective _).comp hψsurj
    have hcentral : ∀ x : ↥J, chevQuotHom 3 L ⟨x.1, hJL x.2⟩ = 1 →
        ψ x ∈ Subgroup.center ↥((J.subgroupOf Y).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y))) := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := hψsurj g
      apply Subtype.ext
      have hmemY : (y.1 * x.1)⁻¹ * (x.1 * y.1) ∈ Y :=
        Y.mul_mem (Y.inv_mem (Y.mul_mem (hJY y.2) (hJY x.2))) (Y.mul_mem (hJY x.2) (hJY y.2))
      have hyx : (y.1 * x.1)⁻¹ * (x.1 * y.1) ∈ GLAPPrimeCoreOf 3 Y :=
        inf_glaPPrimeCoreOf_le Nat.prime_three hYL
          (Subgroup.mem_inf.2 ⟨hmemY, commutator_mem_of_chevQuotHom_eq_one (hJL x.2) hx (hJL y.2)⟩)
      have hmk := mk_eq_of_mem_glaPPrimeCoreOf (Y := Y)
        (Y.mul_mem (hJY y.2) (hJY x.2)) (Y.mul_mem (hJY x.2) (hJY y.2)) hyx
      show QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y) (⟨y.1, hJY y.2⟩ : ↥Y) *
          QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y) (⟨x.1, hJY x.2⟩ : ↥Y) =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y) (⟨x.1, hJY x.2⟩ : ↥Y) *
          QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y) (⟨y.1, hJY y.2⟩ : ↥Y)
      rw [← map_mul, ← map_mul]
      exact hmk
    let πJ : ↥J →* PSimple 3 L := (chevQuotHom 3 L).comp (Subgroup.inclusion hJL)
    have hkerF : πJ.ker ≤ F.ker := by
      intro x hx
      have hx' : chevQuotHom 3 L ⟨x.1, hJL x.2⟩ = 1 := MonoidHom.mem_ker.1 hx
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff (ψ x)).2 (hcentral x hx')
    have hrange : πJ.range ≤ i269Fix φ.range := by
      intro k hk
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hk
      rw [mem_i269Fix]
      intro α hα
      obtain ⟨d, rfl⟩ := MonoidHom.mem_range.1 hα
      rw [hφ]
      exact chevAut_fix_chevQuotHom hDN d.2 (hJL x.2) (hYC x.1 (hJY x.2))
    haveI : Group.IsSolvable ↥πJ.range := isSolvable_of_le_isSolvable hrange
    exact not_isSolvable_quasisimple_mod_center _ hQq (isSolvable_of_factor πJ F hFsurj hkerF)
  show sSup {J : Subgroup G | GLAPComponent 3 Y J} = ⊥
  exact sSup_eq_bot.2 fun J hJ => absurd hJ (key J)

end Reduction

end CFSG.LocalAnalysis.GLTheoremA

end
