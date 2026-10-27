module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L75X4
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DAct
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DE0

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_forall_comm_of_quasisimple {Q : Type*} [Group Q] (hq : CFSG.Open.IsQuasisimple Q)
    (h : ∀ a b : Q, a * b = b * a) : False := by
  have := hq.2
  obtain ⟨c, hc⟩ := exists_ne (1 : Q ⧸ Subgroup.center Q)
  induction c using QuotientGroup.induction_on with | H q => ?_
  apply hc
  exact (QuotientGroup.eq_one_iff q).2 (Subgroup.mem_center_iff.2 fun g => h g q)

theorem glaPComponent_eq_of_le' {X A P : Subgroup G} (hA : GLAPComponent 3 X A)
    (hP : GLAPComponent 3 X P) (h : A ≤ P) : A = P := by
  by_contra hne
  have hlt : A < P := lt_of_le_of_ne h hne
  have hAsnP : IsSubnormal A P := isSubnormal_of_le_of_le hA.2.1 h hP.1
  have hsub : IsSubnormal (barX 3 X A) (barX 3 X P) := isSubnormal_barX 3 hAsnP
  rcases subnormal_eq_or_le_center hsub hP.2.2.1.2.2 with h1 | h1
  · exact hP.2.2.2 A hlt hA.2.1 h1
  · have hAq : CFSG.Open.IsQuasisimple ↥(barX 3 X A) := hA.2.2.1.2.2
    refine not_forall_comm_of_quasisimple hAq fun u v => ?_
    obtain ⟨c, hc, hcu⟩ := h1 u.2
    apply Subtype.ext
    have hv : (v : ↥X ⧸ GLAPPrimeCore 3 ↥X) ∈ barX 3 X P := barX_mono_le h v.2
    have := Subgroup.mem_center_iff.1 hc ⟨v, hv⟩
    have h2 : (⟨v, hv⟩ : ↥(barX 3 X P)) * c = c * ⟨v, hv⟩ := this
    have h3 := congrArg Subtype.val h2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hcu]
    exact h3.symm

section Comps

variable {X B K : Subgroup G} {y : G}

theorem bClosure_subnormal (hB : IsElemAbelian 3 B) (hBX : B ≤ X) (hK : GLAPComponent 3 X K)
    (hy : y ∈ B) (hyN : y ∉ Subgroup.normalizer (K : Set G))
    (h3 : (Subgroup.normalizer (K : Set G)).relIndex B = 3) : IsSubnormal (bClosure B K) X := by
  obtain ⟨hK2, hK3⟩ := phase1_comps hK hBX hy
  have hcl := bClosure_eq_three hB hy hyN h3
  have hΛX : GLAPLayer 3 X ≤ X := sSup_le fun L hL => hL.1
  have hKΛ : bClosure B K ≤ GLAPLayer 3 X := by
    rw [hcl]
    exact sup_le (sup_le (le_sSup hK) (le_sSup hK2)) (le_sSup hK3)
  have hnorm : GLAPLayer 3 X ≤ Subgroup.normalizer (bClosure B K : Set G) := by
    rw [hcl]
    intro g hg
    exact mem_normalizer_sup (mem_normalizer_sup (layer_le_normalizer' hK hg)
      (layer_le_normalizer' hK2 hg)) (layer_le_normalizer' hK3 hg)
  have hΛn : X ≤ Subgroup.normalizer (GLAPLayer 3 X : Set G) := fun g hg =>
    mem_normalizer_iff_gLBConj_eq.2 (by rw [← layer_gLBConj, gLBConj_X_of_mem hg])
  exact IsSubnormal.step hKΛ ((Subgroup.normal_subgroupOf_iff_le_normalizer hKΛ).2 hnorm)
    (IsSubnormal.step hΛX ((Subgroup.normal_subgroupOf_iff_le_normalizer hΛX).2 hΛn)
      (IsSubnormal.refl X))

theorem comp_K0_inf {x : G} {K₀ : Subgroup G} (hB : IsElemAbelian 3 B) (hBX : B ≤ X)
    (hK : GLAPComponent 3 X K) (hy : y ∈ B) (hyN : y ∉ Subgroup.normalizer (K : Set G))
    (h3 : (Subgroup.normalizer (K : Set G)).relIndex B = 3) (hk : K0Data B K x y K₀) :
    GLAPComponent 3 (X ⊓ Subgroup.centralizer ({y} : Set G)) K₀ := by
  have hsn : IsSubnormal K₀ (X ⊓ Subgroup.centralizer ({y} : Set G)) :=
    isSubnormal_trans' hk.comp.2.1 (isSubnormal_inf (bClosure_subnormal hB hBX hK hy hyN h3) _)
  exact Lemma512Ns.glaPComponent_up Nat.prime_three hk.comp
    (inf_le_inf_right _ (bClosure_le_of_comp hB hBX hK hy hyN h3)) hsn

theorem K0_barX_not_comm {x : G} {K₀ : Subgroup G} (hk : K0Data B K x y K₀) {Y : Subgroup G}
    (hK₀Y : K₀ ≤ Y)
    (hcomm : ∀ u ∈ barX 3 Y K₀, ∀ v ∈ barX 3 Y K₀, u * v = v * u) : False := by
  have hq : CFSG.Open.IsQuasisimple (barOf 3 K₀) :=
    (Lemma512Ns.isQuasisimple_barX_iff Nat.prime_three hk.comp.2.1).1 hk.comp.2.2.1.2.2
  refine not_forall_comm_of_quasisimple hq fun a b => ?_
  induction a using QuotientGroup.induction_on with | H k => ?_
  induction b using QuotientGroup.induction_on with | H l => ?_
  have hkY : (k : G) ∈ Y := hK₀Y k.2
  have hlY : (l : G) ∈ Y := hK₀Y l.2
  have hk' : QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y) ⟨k, hkY⟩ ∈ barX 3 Y K₀ :=
    mem_barX_iff.2 ⟨⟨k, hkY⟩, k.2, rfl⟩
  have hl' : QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y) ⟨l, hlY⟩ ∈ barX 3 Y K₀ :=
    mem_barX_iff.2 ⟨⟨l, hlY⟩, l.2, rfl⟩
  have hc := hcomm _ hk' _ hl'
  have hone : QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y)
      (⟨k, hkY⟩ * ⟨l, hlY⟩ * ⟨k, hkY⟩⁻¹ * ⟨l, hlY⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact commutatorElement_eq_one_iff_mul_comm.2 hc
  have h1 := (mem_coreOf_iff (p := 3) (X := Y)
    (⟨k, hkY⟩ * ⟨l, hlY⟩ * ⟨k, hkY⟩⁻¹ * ⟨l, hlY⟩⁻¹)).2 ((QuotientGroup.eq_one_iff _).1 (by exact hone))
  have h2 : (k : G) * l * (k : G)⁻¹ * (l : G)⁻¹ ∈ K₀ ⊓ GLAPPrimeCoreOf 3 Y :=
    ⟨K₀.mul_mem (K₀.mul_mem (K₀.mul_mem k.2 l.2) (K₀.inv_mem k.2)) (K₀.inv_mem l.2), h1⟩
  have h3 := inf_core_le 3 hK₀Y h2
  have h4 : (k * l * k⁻¹ * l⁻¹ : ↥K₀) ∈ GLAPPrimeCore 3 ↥K₀ := (mem_coreOf_iff (p := 3) (X := K₀)
    (k * l * k⁻¹ * l⁻¹)).1 h3
  have h5 : (QuotientGroup.mk (k * l * k⁻¹ * l⁻¹) : barOf 3 K₀) = 1 :=
    (QuotientGroup.eq_one_iff _).2 h4
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h5
  exact (commutatorElement_eq_one_iff_mul_comm.1
    (show ⁅(QuotientGroup.mk k : barOf 3 K₀), (QuotientGroup.mk l : barOf 3 K₀)⁆ = 1 from h5))

end Comps

theorem centralizer_ne_top_of_simple {m : ℕ} (hS : GLStanding G m 3) {y : G} (hy : y ≠ 1) :
    Subgroup.centralizer ({y} : Set G) ≠ ⊤ := by
  intro h
  have := hS.simple
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with h0 | h0
  · apply hy
    have hmem : y ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have : g ∈ Subgroup.centralizer ({y} : Set G) := h ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.1 this
    rw [h0, Subgroup.mem_bot] at hmem
    exact hmem
  · obtain ⟨a, b, hab⟩ := hS.nonabelian
    exact hab (Subgroup.mem_center_iff.1 (h0 ▸ Subgroup.mem_top b : b ∈ Subgroup.center G) a)

theorem mem_A_of_field (iL3 : InputL3U3Facts) {B : Subgroup G} {b : G} {L A : Subgroup G}
    (hx : ExtCtx B b L A) {X K : Subgroup G} (hK : GLAPComponent 3 X K)
    (ht : IsLThreeEps (barOf 3 K)) (hBK : B ≤ Subgroup.normalizer (K : Set G))
    (hFK : B ⊓ L ≤ K)
    (hcov : ∀ a' ∈ A, ∃ h : a' ∈ Subgroup.normalizer (K : Set G), barAut 3 K ⟨a', h⟩ = 1)
    {g : G} (hgB : g ∈ B) (hgf : InducesFieldAut 3 K g) : g ∈ A := by
  have hcentF : A ≤ Subgroup.centralizer ((B ⊓ L : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact (ea_comm hx.Bel (hx.AB ha) hf.1).symm
  have hgAF : g ∈ A ⊔ (B ⊓ L) := by rw [hx.BAF]; exact hgB
  obtain ⟨a', ha', f, hf, rfl⟩ := exists_mul_of_mem_sup hcentF hgAF
  have hfK : f ∈ K := hFK hf
  have hfN : f ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hfK
  have ha'N : a' ∈ Subgroup.normalizer (K : Set G) := hBK (hx.AB ha')
  have hgN : a' * f ∈ Subgroup.normalizer (K : Set G) := Subgroup.mul_mem _ ha'N hfN
  have hmul : barAut 3 K ⟨a' * f, hgN⟩ = barAut 3 K ⟨a', ha'N⟩ * barAut 3 K ⟨f, hfN⟩ := by
    rw [← map_mul]; rfl
  obtain ⟨hN1, h1⟩ := hcov a' ha'
  have hα1 : barAut 3 K ⟨a', ha'N⟩ = 1 := h1
  have hinner : barAut 3 K ⟨a' * f, hgN⟩ ∈ innerAut (barOf 3 K) := by
    rw [hmul, hα1, one_mul, barAut_eq_conj hfK hfN]
    exact ⟨_, rfl⟩
  obtain ⟨hN', hfa⟩ := hgf
  have hα : barAut 3 K ⟨a' * f, hgN⟩ = 1 := (iL3 (barOf 3 K) ht).2.2.1 _ hinner hfa
  have hfeq : barAut 3 K ⟨f, hfN⟩ = 1 := by
    rw [hmul, hα1, one_mul] at hα
    exact hα
  have hf_cq := (Lemma513Ns.mem_centralizerQuot_iff_barAut' 3 ⟨f, hfN⟩).2 hfeq
  have hfO := barOf_centreless iL3 hK ht hfK hf_cq.2.2
  have hFp : IsPGroup 3 ↥(B ⊓ L) := (isPGroup_of_isElemAbelian hx.Bel).to_inf_left
  have hf1 : f ∈ (B ⊓ L) ⊓ GLAPPrimeCoreOf 3 K := ⟨hf, hfO⟩
  rw [pgroup_inf_core_eq_bot K hFp, Subgroup.mem_bot] at hf1
  rw [hf1, mul_one]
  exact ha'

theorem claim_contra (iL3 : InputL3U3Facts) (iK : InputKType) (h514 : Lemma514)
    (h515 : Lemma515) (i183 : Input18_3_4) (iFR : InputFieldRecog) {m : ℕ} {B : Subgroup G}
    {b : G} {L A : Subgroup G} (e : Env m B b L A) {x y : G} (hxB : x ∈ B) (hx1 : x ≠ 1)
    (hxA : x ∉ A) {K : Subgroup G}
    (hK : GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) K) (hyA : y ∈ A)
    (hyN : y ∉ Subgroup.normalizer (K : Set G))
    (h3 : (Subgroup.normalizer (K : Set G)).relIndex B = 3) {R K₀ : Subgroup G}
    (hR : RData (Subgroup.centralizer ({x} : Set G)) B K y R) (hk : K0Data B K x y K₀) :
    False := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := Subgroup.centralizer ({x} : Set G) with hX
  have hy : y ∈ B := e.X.AB hyA
  have hy1 : y ≠ 1 := fun h => hyN (by rw [h]; exact Subgroup.one_mem _)
  have hBX : B ≤ X := fun c hc => by
    rw [hX, Subgroup.mem_centralizer_singleton_iff]; exact ea_comm e.X.Bel hc hxB
  have hx3 : x ^ 3 = 1 := e.X.Bel.2 x hxB
  have hy3 : y ^ 3 = 1 := e.X.Bel.2 y hy
  have hxy : x * y = y * x := ea_comm e.X.Bel hxB hy
  have hKy : GLAPComponent 3 (Subgroup.centralizer ({y} : Set G)) (kOf L A y) :=
    Ka_comp iL3 e.X hyA hy1
  have hKyB : B ≤ Subgroup.normalizer (kOf L A y : Set G) := Ka_B h515 e hyA hy1
  have hKyx : GLBConj x (kOf L A y) = kOf L A y := gLBConj_eq_of_mem_normalizer (hKyB hxB)
  have hKyC : Subgroup.centralizer ({y} : Set G) ≤ Subgroup.normalizer (kOf L A y : Set G) := by
    intro g hg
    refine Ka_N h515 e hyA hy1 (Subgroup.centralizer_le_normalizer _ ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact (Commute.zpow_left (show Commute y g from
      (Subgroup.mem_centralizer_singleton_iff.1 hg).symm) i).eq
  have hYK : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({y} : Set G)) :=
    isKGroup_of_isKProper e.S.kProper (centralizer_ne_top_of_simple e.S hy1)
  have hxCy : x ∈ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hxy
  have hK₀c : GLAPComponent 3 (Subgroup.centralizer ({y} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G)) K₀ := by
    rw [inf_comm]; exact comp_K0_inf e.X.Bel hBX hK hy hyN h3 hk
  obtain ⟨hne1, hne2, hne3, -⟩ := three_conjugates e.X.Bel hy hyN h3
  have hdich := dichotomy_of_input18_3_4 i183 hYK hxCy hx3 hK₀c
  set J₀ := ⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({y} : Set G)), GLBConj g K₀ with hJ₀
  have hK₀J₀ : K₀ ≤ J₀ := by
    have := le_iSup₂ (f := fun g (_ : g ∈ GLAPLayer 3 (Subgroup.centralizer ({y} : Set G))) =>
      GLBConj g K₀) 1 (Subgroup.one_mem _)
    rwa [gLBConj_one] at this
  have hlecq : ∀ P : Subgroup G, GLAPComponent 3 (Subgroup.centralizer ({y} : Set G)) P →
      P ≠ kOf L A y → P ≤ LocalBalance.centralizerQuot (kOf L A y)
        (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({y} : Set G))) := by
    intro P hP hne k hkP
    refine ⟨le_normalizer_of_ne hP hKy hne hkP,
      normalizer_core 3 (Subgroup.le_normalizer (hP.1 hkP)), fun f hf => ?_⟩
    exact commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hKy hP hne.symm
      (Subgroup.commutator_mem_commutator hf hkP)
  have hstar : J₀ = kOf L A y ∨ J₀ ≤ LocalBalance.centralizerQuot (kOf L A y)
      (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({y} : Set G))) := by
    rcases hdich with ⟨Lc, hLc, hK₀L, hJ0, hxL⟩ |
      ⟨L₁, L₂, L₃, h₁, h₂, h₃, h12, h23, h31, hx1', hx2', hx3', hu, -⟩
    · by_cases hLK : Lc = kOf L A y
      · left; rw [hJ0, hLK]
      · right; rw [hJ0]; exact hlecq Lc hLc hLK
    · right
      rw [hu]
      have hL₁ : L₁ ≠ kOf L A y := by
        intro h; apply h12
        calc L₁ = kOf L A y := h
          _ = GLBConj x (kOf L A y) := hKyx.symm
          _ = GLBConj x L₁ := by rw [h]
          _ = L₂ := hx1'
      have hL₂ : L₂ ≠ kOf L A y := by
        intro h; apply h23
        calc L₂ = kOf L A y := h
          _ = GLBConj x (kOf L A y) := hKyx.symm
          _ = GLBConj x L₂ := by rw [h]
          _ = L₃ := hx2'
      have hL₃ : L₃ ≠ kOf L A y := by
        intro h; apply h31
        calc L₃ = kOf L A y := h
          _ = GLBConj x (kOf L A y) := hKyx.symm
          _ = GLBConj x L₃ := by rw [h]
          _ = L₁ := hx3'
      exact sup_le (sup_le (hlecq L₁ h₁ hL₁) (hlecq L₂ h₂ hL₂)) (hlecq L₃ h₃ hL₃)
  have hK₀X : K₀ ≤ X := (hk.le.trans inf_le_left).trans
    (bClosure_le_of_comp e.X.Bel hBX hK hy hyN h3)
  rcases hstar with hJKy | hcq
  ·
    have hK₀Ky : K₀ ≤ kOf L A y := hJKy ▸ hK₀J₀
    have hcompKy : GLAPComponent 3 (kOf L A y ⊓ Subgroup.centralizer ({x} : Set G)) K₀ :=
      glaPComponent_of_le Nat.prime_three hK₀c (le_inf hK₀Ky hK₀X)
        (inf_le_inf_right _ hKy.1)
    have hfield : InducesFieldAut 3 (kOf L A y) x :=
      iFR G (kOf L A y) K₀ x (Ka_type iK e hyA hy1) (hKyB hxB) hx3 hcompKy hk.E9
    by_cases hyb : y ∈ Subgroup.zpowers b
    ·
      have hC := centralizer_eq_of_mem_zpowers (e.X.Bel.2 b e.X.b_mem) e.X.b_ne hyb hy1
      have hKL := kOf_eq_L iL3 e.X hC
      rw [hKL] at hfield hcompKy
      obtain ⟨hPc, -⟩ := e.X.pump x hxB hx1 hfield
      have hK₀Jx : K₀ ≤ GLAPLayer 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) := le_sSup hcompKy
      have hK₀cx : GLAPComponent 3 (X ⊓ Subgroup.centralizer ({y} : Set G)) K₀ :=
        comp_K0_inf e.X.Bel hBX hK hy hyN h3 hk
      have hXK : CFSG.Open.IsKGroup ↥X :=
        isKGroup_of_isKProper e.S.kProper (centralizer_ne_top_of_simple e.S hx1)
      have hyX : y ∈ X := hBX hy
      have hΓP : (⨆ g ∈ GLAPLayer 3 X, GLBConj g K₀) ≤ pumpUp L x := by
        refine iSup₂_le fun g hg => ?_
        exact (gLBConj_mono g hK₀Jx).trans
          (le_iSup₂ (f := fun g (_ : g ∈ GLAPLayer 3 X) =>
            GLBConj g (GLAPLayer 3 (L ⊓ Subgroup.centralizer ({x} : Set G)))) g hg)
      rcases dichotomy_of_input18_3_4 i183 hXK hyX hy3 hK₀cx with
        ⟨L', hL', hK₀L', hΓ, hyL'⟩ |
        ⟨L₁, L₂, L₃, h₁, h₂, h₃', h12, h23, h31, hy1', hy2', hy3', hu, -⟩
      ·
        obtain ⟨hK2, hK3⟩ := phase1_comps hK hBX hy
        have hcl := bClosure_eq_three e.X.Bel hy hyN h3
        have hBXK : K ≤ X := hK.1
        have hBXK2 : GLBConj y K ≤ X := hK2.1
        have hBXK3 : GLBConj y (GLBConj y K) ≤ X := hK3.1
        have hyy : GLBConj y (GLBConj y (GLBConj y K)) = K := by
          rw [gLBConj_gLBConj, gLBConj_gLBConj]
          have : y * (y * y) = 1 := by
            have := hy3; simpa [pow_succ, mul_assoc] using this
          rw [this, gLBConj_one]
        have hL1 : L' ≠ K := fun h => by
          rw [h] at hyL'; exact hne1 hyL'.symm
        have hL2 : L' ≠ GLBConj y K := fun h => by
          rw [h] at hyL'; exact hne3 hyL'.symm
        have hL3 : L' ≠ GLBConj y (GLBConj y K) := fun h => by
          rw [h] at hyL'; exact hne2 (hyy.symm.trans hyL')
        have hcomm : ∀ u ∈ barX 3 X K₀, ∀ v ∈ barX 3 X K₀, u * v = v * u := by
          intro u hu v hv
          have hvL : v ∈ barX 3 X L' := barX_mono_le hK₀L' hv
          have huK : u ∈ barX 3 X (bClosure B K) :=
            barX_mono_le (hk.le.trans inf_le_left) hu
          rw [hcl, barX_sup (sup_le hBXK hBXK2) hBXK3, barX_sup hBXK hBXK2] at huK
          refine (commutes_sup3 (ζ := v) ?_ ?_ ?_ u huK).symm
          · intro w hw; exact barX_comm_of_ne hL' hK hL1 v hvL w hw
          · intro w hw; exact barX_comm_of_ne hL' hK2 hL2 v hvL w hw
          · intro w hw; exact barX_comm_of_ne hL' hK3 hL3 v hvL w hw
        exact K0_barX_not_comm hk hK₀X hcomm
      · have hL1P : L₁ = pumpUp L x :=
          glaPComponent_eq_of_le' h₁ hPc
            ((le_sup_left.trans le_sup_left : L₁ ≤ L₁ ⊔ L₂ ⊔ L₃).trans (hu ▸ hΓP))
        have hL2P : L₂ = pumpUp L x :=
          glaPComponent_eq_of_le' h₂ hPc
            ((le_sup_right.trans le_sup_left : L₂ ≤ L₁ ⊔ L₂ ⊔ L₃).trans (hu ▸ hΓP))
        exact h12 (hL1P.trans hL2P.symm)
    ·
      have hcov := (h514 G m e.S e.C B e.B1 b L A e.w y hyA hy1).2 hyb
      refine hxA (mem_A_of_field iL3 e.X hKy (Ka_type iK e hyA hy1) hKyB (F_le_Ka e.X y) ?_ hxB
        hfield)
      intro a' ha'
      have ha'N : a' ∈ Subgroup.normalizer (kOf L A y : Set G) := hKyB (e.X.AB ha')
      refine ⟨ha'N, barAut_eq_one_of_cover (jOf_le_kOf' L A y) hcov ha'N fun j hj => ?_⟩
      have hjC : j ∈ Subgroup.centralizer (A : Set G) := (jOf_le' L A hj).2
      exact Subgroup.mem_centralizer_iff.1 hjC a' ha'
  ·
    have hFcq : B ⊓ L ≤ B ⊓ LocalBalance.centralizerQuot K₀ (GLAPPrimeCoreOf 3 K₀) := by
      intro f hf
      refine ⟨hf.1, hk.B_inv hf.1, normalizer_core 3 (hk.B_inv hf.1), fun k hkK => ?_⟩
      have hfKy : f ∈ kOf L A y := F_le_Ka e.X y hf
      have h1 := (hcq (hK₀J₀ hkK)).2.2 f hfKy
      have h2 : k * f * k⁻¹ * f⁻¹ ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({y} : Set G)) := by
        have := (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({y} : Set G))).inv_mem h1
        simpa [mul_assoc] using this
      have h3' : k * f * k⁻¹ * f⁻¹ ∈ K₀ := by
        have h1' := (Subgroup.mem_normalizer_iff.1 (hk.B_inv hf.1) k⁻¹).1 (K₀.inv_mem hkK)
        have := K₀.mul_mem hkK h1'
        simpa [mul_assoc] using this
      exact inf_core_le 3 (hk.le.trans inf_le_right |>.trans le_rfl) ⟨h3', h2⟩
    have hxN : x ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_le_centralizer hK.1
    have hne' : Subgroup.zpowers x ≠ Subgroup.zpowers y := by
      intro h
      apply hyN
      have : y ∈ Subgroup.zpowers x := h ▸ Subgroup.mem_zpowers y
      exact (Subgroup.zpowers_le.2 hxN) this
    have h9 := card_zpowers_sup hxy hx3 hy3 hx1 hy1 hne'
    have hFle : B ⊓ L ≤ Subgroup.zpowers x ⊔ Subgroup.zpowers y := hk.cq ▸ hFcq
    have hFeq : B ⊓ L = Subgroup.zpowers x ⊔ Subgroup.zpowers y :=
      Subgroup.eq_of_le_of_card_ge hFle (by rw [h9, e.X.Fc])
    have hyF : y ∈ B ⊓ L := by
      rw [hFeq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    have : y ∈ A ⊓ (B ⊓ L) := ⟨hyA, hyF⟩
    rw [e.X.AF, Subgroup.mem_bot] at this
    exact hy1 this

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
