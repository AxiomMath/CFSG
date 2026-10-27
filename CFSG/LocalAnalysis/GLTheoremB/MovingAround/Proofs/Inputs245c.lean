module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs245b
import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenDataAux

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs245c

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.AGLEmbedding

section Map

variable {X : Type} [Group X] [Finite X]

theorem map_glbCore_le {p : ℕ} (hp : 1 < p) (k : ℕ) {K P : Subgroup X} {S : Subgroup ↥K}
    (hSP : S.map K.subtype ≤ P) : (GLBCore p k S).map K.subtype ≤ GLBCore p k P := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le ?_
  rintro _ ⟨Q, hQS, hQk, rfl⟩
  rw [← Subgroup.map_le_iff_le_comap]
  refine (Subgroup.le_normalizer_map K.subtype).trans ?_
  exact le_sSup ⟨Q.map K.subtype, (Subgroup.map_mono hQS).trans hSP,
    hQk.trans (CFSG.SectionRank.pRank_le_map hp K.subtype K.subtype_injective Q), rfl⟩

theorem map_x0_le {p : ℕ} (hp : 1 < p) {K P : Subgroup X} {S : Subgroup ↥K}
    (hSP : S.map K.subtype ≤ P) : (Inputs245.x0 p S).map K.subtype ≤ Inputs245.x0 p P := by
  rw [Inputs245.x0, Inputs245.x0, Subgroup.map_sup]
  refine sup_le ((map_glbCore_le hp 4 hSP).trans le_sup_left) ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun E => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hE => ?_
  have hE' : IsEkIn p 4 P (E.map K.subtype) :=
    ⟨(Subgroup.map_mono hE.1).trans hSP, CFSG.SectionRank.isElemAbelian_map hE.2.1 K.subtype,
      by rw [Subgroup.card_map_of_injective K.subtype_injective, hE.2.2]⟩
  exact (map_glbCore_le hp 2 le_rfl).trans
    (le_sup_of_le_right (le_iSup₂_of_le (E.map K.subtype) hE' le_rfl))

end Map

@[expose] def CoverX0 (Y : Type) [Group Y] (p : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (π : K →* Y), Function.Surjective π →
    π.ker = Subgroup.center K → Group.IsPerfect K → Subgroup.center K ≠ ⊥ →
    IsPGroup p (Subgroup.center K) → IsCyclic (Subgroup.center K) →
    ∀ T : Sylow p K, Inputs245.x0 p (T : Subgroup K) = ⊤

theorem coverX0_of_mulEquiv {Y Z : Type} [Group Y] [Group Z] {p : ℕ} (e : Y ≃* Z)
    (h : CoverX0 Y p) : CoverX0 Z p := by
  intro K _ _ π hπ hker hperf hZ1 hZp hZc T
  refine h K (e.symm.toMonoidHom.comp π) (e.symm.surjective.comp hπ) ?_ hperf hZ1 hZp hZc T
  rw [← hker]
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
  exact ⟨fun h => e.symm.injective (by rw [h, map_one]), fun h => by rw [h, map_one]⟩

section Claim

variable {X : Type} [Group X] [Finite X]

theorem inf_centralizer_le_pCoreOf (hO : GLAPPrimeCore 3 X = ⊥) {P K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hPK : P ≤ Subgroup.normalizer (K : Set X)) :
    K ⊓ Subgroup.centralizer (K : Set X) ≤ pCoreOf 3 (P ⊔ K) := by
  refine Inputs245b.le_pCoreOf_of_le_normalizer (inf_le_left.trans le_sup_right) (sup_le ?_ ?_) ?_
  · intro g hg
    exact Inputs245.mem_normalizer_inf (hPK hg) (Inputs245b.mem_normalizer_centralizer (hPK hg))
  · intro g hg
    exact Inputs245.mem_normalizer_inf (Subgroup.le_normalizer hg)
      (Inputs245b.mem_normalizer_centralizer (Subgroup.le_normalizer hg))
  · have hZp := Inputs245b.isPGroup_center_of_component Nat.prime_three hO hK
    intro x
    obtain ⟨k, hk⟩ := hZp ⟨⟨x, x.2.1⟩, Subgroup.mem_center_iff.2 fun g =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.1 x.2.2) g g.2)⟩
    refine ⟨k, Subtype.ext ?_⟩
    have := congrArg (fun y : Subgroup.center ↥K => ((y : ↥K) : X)) hk
    simpa using this

theorem isCyclic_center_of_component (hO : GLAPPrimeCore 3 X = ⊥) {P K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hPK : P ≤ Subgroup.normalizer (K : Set X))
    (hcyc : IsCyclic ↥(pCoreOf 3 (P ⊔ K))) : IsCyclic ↥(Subgroup.center ↥K) := by
  have hle : (Subgroup.center ↥K).map K.subtype ≤ pCoreOf 3 (P ⊔ K) := by
    refine le_trans ?_ (inf_centralizer_le_pCoreOf hO hK hPK)
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z.2, Subgroup.mem_centralizer_iff.2 fun k hk =>
      congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨k, hk⟩)⟩
  haveI := hcyc
  haveI : IsCyclic ↥((Subgroup.center ↥K).map K.subtype) := Subgroup.isCyclic_of_le hle
  exact isCyclic_of_injective
    (Subgroup.equivMapOfInjective (Subgroup.center ↥K) K.subtype K.subtype_injective).toMonoidHom
    (Subgroup.equivMapOfInjective (Subgroup.center ↥K) K.subtype K.subtype_injective).injective

theorem le_x0_of_coverX0 (hO : GLAPPrimeCore 3 X = ⊥) {P : Subgroup X} (hP : IsSylowIn 3 ⊤ P)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) (hPK : P ≤ Subgroup.normalizer (K : Set X))
    (hZK : Subgroup.center ↥K ≠ ⊥) (hcyc : IsCyclic ↥(pCoreOf 3 (P ⊔ K))) {Y : Type} [Group Y]
    (e : ↥K ⧸ Subgroup.center ↥K ≃* Y) (h : CoverX0 Y 3) : K ≤ Inputs245.x0 3 P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal (Inputs245.sylowOf hP)
    (CFSG.Open.IsSubnormal.top_iff.1 hK.2.1)
  have hSP : (S : Subgroup ↥K).map K.subtype ≤ P := by
    rw [hS, Inputs245.coe_sylowOf]
    exact inf_le_left
  let π : ↥K →* Y := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center ↥K := by
    ext x
    simp [π]
  have hperf : Group.IsPerfect ↥K := ⟨hK.2.2.1⟩
  have htop := h ↥K π hπ hker hperf hZK
    (Inputs245b.isPGroup_center_of_component Nat.prime_three hO hK)
    (isCyclic_center_of_component hO hK hPK hcyc) S
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥K) ∈ Inputs245.x0 3 (S : Subgroup ↥K) := by
    rw [htop]
    exact Subgroup.mem_top _
  exact map_x0_le (by norm_num) hSP ⟨⟨x, hx⟩, hmem, rfl⟩

end Claim

@[expose] def CoverPointDatumA (Y : Type) [Group Y] (p : ℕ) : Prop :=
  ∃ (D : ModuleSpec Y p) (k : ℕ) (b : Fin k → Y) (l : Fin k → ℕ)
    (h : (j : Fin k) → Fin (l j) → Y) (e : (j : Fin k) → Fin (l j) → ℕ),
    3 ≤ D.n ∧ D.NoAlt ∧ D.NoFun ∧ (∀ j, b j ∈ D.span ∧ b j ≠ 1) ∧
    (∀ j i, h j i * b j * (h j i)⁻¹ = b j ^ e j i) ∧
    Subgroup.closure (Set.range D.g ∪ ⋃ j, Set.range (h j)) = ⊤

section Datum

variable {K Y : Type} [Group K] [Finite K] [Group Y] [Finite Y] {p : ℕ}

theorem x0_eq_top_of_datum (hp : p.Prime) (hp2 : p ≠ 2) (π : K →* Y) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K) (hZ1 : Subgroup.center K ≠ ⊥)
    (hZp : IsPGroup p (Subgroup.center K)) (hZc : IsCyclic (Subgroup.center K))
    (D : ModuleSpec Y p) {k : ℕ} (b : Fin k → Y) {l : Fin k → ℕ}
    (h : (j : Fin k) → Fin (l j) → Y) (e : (j : Fin k) → Fin (l j) → ℕ) (hn : 3 ≤ D.n)
    (hA : D.NoAlt) (hF : D.NoFun) (hb : ∀ j, b j ∈ D.span ∧ b j ≠ 1)
    (hconj : ∀ j i, h j i * b j * (h j i)⁻¹ = b j ^ e j i)
    (hgen : Subgroup.closure (Set.range D.g ∪ ⋃ j, Set.range (h j)) = ⊤) {T : Subgroup K}
    (hÂT : D.span.comap π ≤ T) : Inputs245.x0 p T = ⊤ := by
  have := Fact.mk hp
  have hπZ : ∀ z ∈ Subgroup.center K, π z = 1 := fun z hz =>
    MonoidHom.mem_ker.mp (hker.symm ▸ hz)
  have hcomm := D.commute_of_noAlt π hp hp2 hπ hker hZp hZc hA
  set A : Subgroup K := omegaOf (D.span.comap π) hcomm p
  have hAel : IsElemAbelian p A := isElemAbelian_omegaOf
  have hA4 : p ^ 4 ≤ Nat.card A :=
    (Nat.pow_le_pow_right hp.pos (by omega : 4 ≤ D.n + 1)).trans
      (D.pow_succ_le_card_omegaOf π hp hp2 hπ hker hZ1 hZp hZc hcomm hF)
  have hAT : A ≤ T := omegaOf_le.trans hÂT
  have hrkA : 4 ≤ CFSG.Open.pRank p A := le_pRank_of_pow_le_card hp le_rfl hAel hA4
  have hNA : Subgroup.normalizer ((D.span.comap π : Subgroup K) : Set K) ≤ Inputs245.x0 p T :=
    (le_normalizer_omegaOf le_rfl).trans (Inputs245.normalizer_le_x0 hAT hrkA)
  have hNQ : ∀ j, Subgroup.normalizer
      (((Subgroup.zpowers (b j)).comap π : Subgroup K) : Set K) ≤ Inputs245.x0 p T := by
    intro j
    have hcQ := mul_comm_of_mem_comap_zpowers π hπ hker (b j)
    have hQÂ : (Subgroup.zpowers (b j)).comap π ≤ D.span.comap π :=
      Subgroup.comap_mono (Subgroup.zpowers_le.mpr (hb j).1)
    have hDA : omegaOf ((Subgroup.zpowers (b j)).comap π) hcQ p ≤ A :=
      fun x hx => ⟨hQÂ hx.1, hx.2⟩
    have h2 : 2 ≤ CFSG.Open.pRank p (omegaOf ((Subgroup.zpowers (b j)).comap π) hcQ p) := by
      refine le_pRank_of_pow_le_card hp le_rfl isElemAbelian_omegaOf ?_
      have h := D.mul_card_map_le_card_omegaOf π hp hp2 hπ hker hZ1 hZp hZc hF hQÂ
        (hker ▸ Subgroup.ker_le_comap π _) hcQ
      rwa [Subgroup.map_comap_eq_self_of_surjective hπ, Nat.card_zpowers,
        orderOf_eq_prime (D.pow_eq_one_of_mem (hb j).1) (hb j).2, ← pow_two] at h
    have hN : Subgroup.normalizer
        ((omegaOf ((Subgroup.zpowers (b j)).comap π) hcQ p : Subgroup K) : Set K) ≤
          GLBCore p 2 A := le_sSup ⟨_, hDA, h2, rfl⟩
    exact (le_normalizer_omegaOf le_rfl).trans
      (hN.trans (Inputs245b.glbCore_two_le_x0 hp hAT hAel hA4))
  have hZ : Subgroup.center K ≤ Inputs245.x0 p T := fun z hz =>
    hNA (Subgroup.le_normalizer_comap π (by rw [Subgroup.mem_comap, hπZ z hz]; exact one_mem _))
  have hmap : (Inputs245.x0 p T).map π = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro u (⟨i, rfl⟩ | hu)
    · refine ⟨Function.surjInv hπ (D.g i), hNA (Subgroup.le_normalizer_comap π ?_),
        Function.surjInv_eq hπ _⟩
      rw [Subgroup.mem_comap, Function.surjInv_eq hπ]
      exact D.g_mem_normalizer i
    · obtain ⟨j, i, rfl⟩ := Set.mem_iUnion.mp hu
      refine ⟨Function.surjInv hπ (h j i), hNQ j (Subgroup.le_normalizer_comap π ?_),
        Function.surjInv_eq hπ _⟩
      rw [Subgroup.mem_comap, Function.surjInv_eq hπ]
      exact mem_normalizer_zpowers_of_conj_eq_pow (hconj j i)
  rw [← Subgroup.comap_map_eq_self (H := Inputs245.x0 p T) (hker ▸ hZ), hmap,
    Subgroup.comap_top]

theorem comap_map_conj_le (π : K →* Y) (g : K) {H : Subgroup Y} {T : Subgroup K}
    (hHT : H.comap π ≤ T) :
    (H.map (MulAut.conj (π g)).toMonoidHom).comap π ≤ T.map (MulAut.conj g).toMonoidHom := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hx)
  refine ⟨g⁻¹ * x * g, hHT ?_, ?_⟩
  · rw [Subgroup.mem_comap, map_mul, map_mul, ← hyx, map_inv]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rwa [show (π g)⁻¹ * (π g * y * (π g)⁻¹) * π g = y by group]
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

end Datum

theorem coverX0_of_coverPointDatumA {Y : Type} [Group Y] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hdat : CoverPointDatumA Y p) : CoverX0 Y p := by
  intro K _ _ π hπ hker _ hZ1 hZp hZc T
  obtain ⟨D, k, b, l, h, e, hn, hA, hF, hb, hconj, hgen⟩ := hdat
  have := Fact.mk hp
  have : Finite Y := Finite.of_surjective π hπ
  obtain ⟨T₀, hT₀⟩ := (D.isPGroup_comap π (hker ▸ hZp)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K T₀ T
  have hT : (T : Subgroup K) = (T₀ : Subgroup K).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  let f : Y →* Y := (MulAut.conj (π g)).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj (π g)).injective
  refine x0_eq_top_of_datum hp hp2 π hπ hker hZ1 hZp hZc (D.map f hf) (fun j => f (b j))
    (fun j i => f (h j i)) e hn hA hF (fun j => ⟨?_, ?_⟩) (fun j i => ?_) ?_ ?_
  · rw [D.map_span f hf]
    exact Subgroup.mem_map_of_mem f (hb j).1
  · intro h1
    exact (hb j).2 (hf (by rw [h1, map_one]))
  · show f (h j i) * f (b j) * (f (h j i))⁻¹ = f (b j) ^ e j i
    rw [← map_inv, ← map_mul, ← map_mul, hconj, map_pow]
  · have hrange : Set.range (D.map f hf).g ∪ ⋃ j, Set.range (fun i => f (h j i)) =
        f '' (Set.range D.g ∪ ⋃ j, Set.range (h j)) := by
      rw [Set.image_union, Set.image_iUnion, ← Set.range_comp]
      congr 1
      refine Set.iUnion_congr fun j => ?_
      rw [← Set.range_comp]
      rfl
    rw [hrange, ← MonoidHom.map_closure, hgen, Subgroup.map_top_of_surjective]
    exact (MulAut.conj (π g)).surjective
  · rw [D.map_span f hf, hT]
    exact comap_map_conj_le π g hT₀

section Sound

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native CFSG.Blueprint CFSG.SectionRank.LocalWitness CFSG.AGLEmbedding.R3

@[expose] def cpNoAlt (D : CpSpec) : Bool :=
  (nonzeroTriples D.p).all fun v => D.m.acts.any fun g => !g.fixes D.p v.1 v.2.1 v.2.2

theorem noAlt_of_cpNoAlt {D : CpSpec} [Fact D.p.Prime] (h : cpNoAlt D = true)
    (u : Fin 3 → ZMod D.p)
    (hu : ∀ g ∈ D.m.acts, (actMat D.p g).transpose * alt3 u * actMat D.p g = alt3 u) : u = 0 := by
  by_contra hne
  have hv : ((u 0).val, (u 1).val, (u 2).val) ∈ nonzeroTriples D.p := by
    rw [mem_nonzeroTriples]
    refine ⟨ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _, ?_⟩
    rintro ⟨h0, h1, h2⟩
    apply hne
    ext k
    fin_cases k
    · exact (ZMod.val_eq_zero _).1 h0
    · exact (ZMod.val_eq_zero _).1 h1
    · exact (ZMod.val_eq_zero _).1 h2
  unfold cpNoAlt at h
  obtain ⟨g, hg, hgf⟩ := List.any_eq_true.1 (List.all_eq_true.1 h _ hv)
  rw [fixes_of_invariant g u (hu g hg)] at hgf
  exact Bool.false_ne_true hgf

variable {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ} (Sp : OpsSpec O c d)
  {sA sB : String} {nregs : ℕ} {prog : List Op} {D : CpSpec}

include Sp in
theorem coverPointDatumA_of_check (hp : D.p.Prime) (hp2 : D.p ≠ 2)
    (h : cpCheck O sA sB nregs prog D = true) (hNF : D.noFun = true) (hNA : cpNoAlt D = true) :
    CoverPointDatumA (NativeSporadic.seedMonoid c d 1 sA sB)ˣ D.p := by
  have : Fact D.p.Prime := ⟨hp⟩
  unfold cpCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hC, hrA⟩, hrB⟩, hAeq⟩, hBeq⟩, hwf⟩ := h
  let C : MCert := ⟨nregs, prog, D.facts⟩
  have hC' : mcertCheck O sA sB C = true := hC
  have fordA : MFact.ord D.rA D.oA ∈ D.facts := by simp [CpSpec.facts]
  have fordB : MFact.ord D.rB D.oB ∈ D.facts := by simp [CpSpec.facts]
  have feA : MFact.eq [(D.rA, 1)] D.wA ∈ D.facts := by simp [CpSpec.facts]
  have feB : MFact.eq [(D.rB, 1)] D.wB ∈ D.facts := by simp [CpSpec.facts]
  have hmodf : ∀ f ∈ D.m.facts D.p, f ∈ D.facts := by
    intro f hf
    simp only [CpSpec.facts, List.mem_append]
    exact Or.inl (Or.inl (Or.inr hf))
  have hptf : ∀ b ∈ D.pts, ∀ f ∈ b.facts D.p, f ∈ D.facts := by
    intro b hb f hf
    simp only [CpSpec.facts, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inr ⟨b, hb, hf⟩)
  have hactord : ∀ g ∈ D.m.acts, MFact.ord g.reg g.ord ∈ D.facts := by
    intro g hg
    apply hmodf
    simp only [Mod.facts, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨g, hg, by simp⟩
  have hhord : ∀ b ∈ D.pts, ∀ k ∈ b.hs, MFact.ord k.reg k.ord ∈ D.facts := by
    intro b hb k hk
    apply hptf b hb
    simp only [CpPt.facts, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨k, hk, by simp⟩
  have hb0 : MFact.ord D.m.b0 D.p ∈ D.facts := hmodf _ (by simp [Mod.facts])
  have hb1 : MFact.ord D.m.b1 D.p ∈ D.facts := hmodf _ (by simp [Mod.facts])
  have hb2 : MFact.ord D.m.b2 D.p ∈ D.facts := hmodf _ (by simp [Mod.facts])
  unfold CpSpec.wf at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
  obtain ⟨⟨⟨⟨-, hptwf⟩, hind⟩, hderwf⟩, hseedwf⟩ := hwf
  have hindep : ∀ v ∈ nonzeroTriples D.p, ∃ q ∈ D.m.indep,
      q.1 = v.1 ∧ q.2.1 = v.2.1 ∧ q.2.2.1 = v.2.2 := by
    intro v hv
    obtain ⟨q, hq, hqv⟩ := List.any_eq_true.1 (List.all_eq_true.1 hind v hv)
    simp only [Bool.and_eq_true, beq_iff_eq] at hqv
    exact ⟨q, hq, hqv.1.1, hqv.1.2, hqv.2⟩
  obtain ⟨DS, h3, hact, hspan⟩ := exists_moduleSpec_core Sp hC' D.m hmodf hindep
  have hNFDS : DS.NoFun := noFun_of_entries h3 DS.M D.m.acts
    (fun g hg => by obtain ⟨j, -, hj⟩ := hact g hg; exact ⟨j, hj⟩)
    (fun v hv => noFun_of_bool hNF v hv)
  have hNADS : DS.NoAlt := noAlt_of_entries hp2 h3 DS.M D.m.acts
    (fun g hg => by obtain ⟨j, -, hj⟩ := hact g hg; exact ⟨j, hj⟩)
    (fun u hu => noAlt_of_cpNoAlt hNA u hu)
  have hbasis : ∀ w : Word, (∀ q ∈ w, q.1 = D.m.b0 ∨ q.1 = D.m.b1 ∨ q.1 = D.m.b2) →
      HasOrd C w := by
    intro w hw q hq
    rcases hw q hq with h | h | h
    · exact ⟨D.p, h ▸ hb0⟩
    · exact ⟨D.p, h ▸ hb1⟩
    · exact ⟨D.p, h ▸ hb2⟩
  have hptspan : ∀ b ∈ D.pts, regUnit Sp hC' b.reg ∈ DS.span ∧ regUnit Sp hC' b.reg ≠ 1 := by
    intro b hb
    have hbo : MFact.ord b.reg D.p ∈ C.facts := hptf b hb _ (by simp [CpPt.facts])
    have hbw := List.all_eq_true.1 hptwf b hb
    have hw' : ∀ q ∈ b.w, q.1 = D.m.b0 ∨ q.1 = D.m.b1 ∨ q.1 = D.m.b2 := by
      intro q hq
      have := List.all_eq_true.1 hbw q hq
      simpa [Bool.or_eq_true, beq_iff_eq, or_assoc] using this
    refine ⟨?_, ?_⟩
    · have hf : MFact.eq [(b.reg, 1)] b.w ∈ C.facts := hptf b hb _ (by simp [CpPt.facts])
      have hu : HasOrd C [(b.reg, 1)] := fun a ha => by
        simp only [List.mem_singleton] at ha; rw [ha]; exact ⟨D.p, hbo⟩
      have := regUnit_eq Sp hC' hf hu (hbasis b.w hw')
      have e : wordUnit Sp hC' [(b.reg, 1)] = regUnit Sp hC' b.reg := by simp [wordUnit]
      rw [e] at this
      rw [this, hspan]
      refine CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup Sp hC' _ b.w fun q hq => ?_
      apply Subgroup.subset_closure
      rcases hw' q hq with h | h | h
      · exact ⟨0, by simp [Mod.basis, h]⟩
      · exact ⟨1, by simp [Mod.basis, h]⟩
      · exact ⟨2, by simp [Mod.basis, h]⟩
    · have hf : MFact.ne [(b.reg, 1)] [] b.t ∈ C.facts := hptf b hb _ (by simp [CpPt.facts])
      have hu : HasOrd C [(b.reg, 1)] := fun a ha => by
        simp only [List.mem_singleton] at ha; rw [ha]; exact ⟨D.p, hbo⟩
      have := regUnit_ne Sp hC' hf hu (hasOrd_nil C)
      simpa [wordUnit] using this
  let hh : (j : Fin D.pts.length) → Fin (D.pts.get j).hs.length →
      (certMonoid c d sA sB)ˣ := fun j i => regUnit Sp hC' ((D.pts.get j).hs.get i).reg
  have hactG : ∀ r ∈ D.actRegs, regUnit Sp hC' r ∈
      Subgroup.closure (Set.range DS.g ∪ ⋃ j, Set.range (hh j)) ∧
      ∃ o, MFact.ord r o ∈ C.facts := by
    intro r hr
    rcases List.mem_append.1 hr with h1 | h1
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 h1
      obtain ⟨j, hj, -⟩ := hact g hg
      exact ⟨Subgroup.subset_closure (Or.inl ⟨j, by rw [hj]⟩), g.ord, hactord g hg⟩
    · obtain ⟨b, hb, h2⟩ := List.mem_flatMap.1 h1
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 h2
      obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hb
      obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hk
      exact ⟨Subgroup.subset_closure (Or.inr (Set.mem_iUnion.2 ⟨j, ⟨i, rfl⟩⟩)), _,
        hhord _ hb _ hk⟩
  have hderf : ∀ e ∈ D.der, ∀ f ∈ e.facts, f ∈ D.facts := by
    intro e he f hf
    simp only [CpSpec.facts, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨e, he, hf⟩
  have hderG := der_mem Sp hC'
    (Subgroup.closure (Set.range DS.g ∪ ⋃ j, Set.range (hh j))) D.der D.actRegs hderf hactG hderwf
  have hseedG : ∀ q ∈ D.wA ++ D.wB, regUnit Sp hC' q.1 ∈
      Subgroup.closure (Set.range DS.g ∪ ⋃ j, Set.range (hh j)) ∧
      ∃ o, MFact.ord q.1 o ∈ C.facts := by
    intro q hq
    rcases List.mem_append.1 (List.contains_iff_mem.1 (List.all_eq_true.1 hseedwf q hq)) with h | h
    · exact hactG q.1 h
    · obtain ⟨e, he, hq1⟩ := List.mem_map.1 h
      rw [← hq1]
      exact hderG e he
  have hOrdGens : ∀ w : Word, (∀ q ∈ w, q ∈ D.wA ++ D.wB) → HasOrd C w :=
    fun w hw q hq => (hseedG q (hw q hq)).2
  have hΓreg : ∀ q ∈ D.wA ++ D.wB, regUnit Sp hC' q.1 ∈
      Subgroup.closure (Set.range DS.g ∪ ⋃ j, Set.range (hh j)) :=
    fun q hq => (hseedG q hq).1
  have hrA' : D.rA < C.nregs := hrA
  have hrB' : D.rB < C.nregs := hrB
  have hvalA : valHom (certMonoid c d sA sB) (regUnit Sp hC' D.rA) =
      NativeSporadic.decode c d 1 sA := by
    rw [val_regUnit Sp hC' fordA, Sp.toMat_eq (reg_ok Sp hC' hrA').1 (Sp.decode_wf sA) hAeq,
      Sp.toMat_decode]
  have hvalB : valHom (certMonoid c d sA sB) (regUnit Sp hC' D.rB) =
      NativeSporadic.decode c d 1 sB := by
    rw [val_regUnit Sp hC' fordB, Sp.toMat_eq (reg_ok Sp hC' hrB').1 (Sp.decode_wf sB) hBeq,
      Sp.toMat_decode]
  have htop := CFSG.RankThree.PartOne.CTP.Fus.closure_pair_units_eq_top (certMonoid c d sA sB) rfl
    (regUnit Sp hC' D.rA) (regUnit Sp hC' D.rB) hvalA hvalB
  have hAw : regUnit Sp hC' D.rA = wordUnit Sp hC' D.wA := by
    have := regUnit_eq Sp hC' feA (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨D.oA, fordA⟩)
      (hOrdGens D.wA fun q hq => List.mem_append.2 (Or.inl hq))
    simpa [wordUnit] using this
  have hBw : regUnit Sp hC' D.rB = wordUnit Sp hC' D.wB := by
    have := regUnit_eq Sp hC' feB (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨D.oB, fordB⟩)
      (hOrdGens D.wB fun q hq => List.mem_append.2 (Or.inr hq))
    simpa [wordUnit] using this
  refine ⟨DS, D.pts.length, fun j => regUnit Sp hC' (D.pts.get j).reg,
    fun j => (D.pts.get j).hs.length, hh, fun j i => ((D.pts.get j).hs.get i).e,
    h3.ge, hNADS, hNFDS, fun j => hptspan _ (List.get_mem _ _), ?_, ?_⟩
  · intro j i
    show regUnit Sp hC' ((D.pts.get j).hs.get i).reg * regUnit Sp hC' (D.pts.get j).reg *
      (regUnit Sp hC' ((D.pts.get j).hs.get i).reg)⁻¹ =
        regUnit Sp hC' (D.pts.get j).reg ^ ((D.pts.get j).hs.get i).e
    have hb := List.get_mem D.pts j
    have hk := List.get_mem (D.pts.get j).hs i
    have hf : MFact.conj ((D.pts.get j).hs.get i).reg [((D.pts.get j).reg, 1)]
        [((D.pts.get j).reg, ((D.pts.get j).hs.get i).e)] ∈ C.facts := by
      apply hptf _ hb
      simp only [CpPt.facts, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨_, hk, by simp⟩
    have hbo : MFact.ord (D.pts.get j).reg D.p ∈ C.facts := hptf _ hb _ (by simp [CpPt.facts])
    have hu : HasOrd C [((D.pts.get j).reg, 1)] := fun a ha => by
      simp only [List.mem_singleton] at ha; rw [ha]; exact ⟨D.p, hbo⟩
    have hw : HasOrd C [((D.pts.get j).reg, ((D.pts.get j).hs.get i).e)] := fun a ha => by
      simp only [List.mem_singleton] at ha; rw [ha]; exact ⟨D.p, hbo⟩
    have := regUnit_conj Sp hC' hf (hhord _ hb _ hk) hu hw
    simpa [wordUnit] using this
  · refine eq_top_iff.mpr ?_
    rw [← htop, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · rw [hAw]
      exact CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup Sp hC' _ D.wA fun q hq =>
        hΓreg q (List.mem_append.2 (Or.inl hq))
    · rw [hBw]
      exact CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup Sp hC' _ D.wB fun q hq =>
        hΓreg q (List.mem_append.2 (Or.inr hq))

end Sound

@[expose] def ThreeCoverX0Table : Prop :=
  ∀ i : TauCeti.CFSGIndex, GL83.I243.IsThreeCoverIndex i → i ≠ .sporadic .J3 →
    i ≠ .sporadic .ONan → IsSimpleGroup i.Group → CoverX0 i.Group 3

theorem threeCoverX0Table_of
    (hMcL : IsSimpleGroup (TauCeti.CFSGIndex.sporadic .McL).Group →
      CoverX0 (TauCeti.CFSGIndex.sporadic .McL).Group 3)
    (hSuz : IsSimpleGroup (TauCeti.CFSGIndex.sporadic .Suz).Group →
      CoverX0 (TauCeti.CFSGIndex.sporadic .Suz).Group 3)
    (hFi22 : IsSimpleGroup (TauCeti.CFSGIndex.sporadic .Fi22).Group →
      CoverX0 (TauCeti.CFSGIndex.sporadic .Fi22).Group 3)
    (hFi24 : IsSimpleGroup (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group →
      CoverX0 (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group 3)
    (hU43 : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid), q.card = 3 →
      IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group →
      CoverX0 (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group 3)
    (hO73 : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.B 3 q).Valid), q.card = 3 →
      IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.B 3 q, hv⟩).Group →
      CoverX0 (TauCeti.CFSGIndex.lie ⟨.B 3 q, hv⟩).Group 3)
    (hG23 : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid), q.card = 3 →
      IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group →
      CoverX0 (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group 3) :
    ThreeCoverX0Table := by
  intro i hi hJ hN
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | ⟨q, hv, hq, rfl⟩ | ⟨q, hv, hq, rfl⟩ |
    ⟨q, hv, hq, rfl⟩
  · exact hMcL
  · exact hSuz
  · exact hFi22
  · exact hFi24
  · exact absurd rfl hJ
  · exact absurd rfl hN
  · exact hU43 q hv hq
  · exact hO73 q hv hq
  · exact hG23 q hv hq

theorem input24_5_compCover_of_table (h : ThreeCoverX0Table) : Inputs245b.Input24_5_compCover := by
  intro X _ _ _ hO _ _ P hP _ K hK hPK hZK hcyc ⟨i, hi, hJ, hN, ⟨e⟩⟩
  have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.2.2.2
  exact le_x0_of_coverX0 hO hP hK hPK hZK hcyc e (h i hi hJ hN e.symm.isSimpleGroup)

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs245c
