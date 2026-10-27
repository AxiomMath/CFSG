module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6Chain
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6Frame
public import CFSG.ClassicalInvolution.RouteD.TypeUChain

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.ClassicalInvolution.Phan
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Steinberg.Exceptional
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

structure IsTE6Base (p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f) {G : Type} [Group G]
    (Ω : Set (Subgroup G)) (K : Subgroup G) (z : G) (V : Fin 3 → Subgroup G) : Prop where
  mem : V 0 ∈ Ω
  comm : Commutes (V 0) (V 2)
  pair_long : ∃ W, UnitaryB2BlockStandardPair (frobQ p f) (frobQ_frobQ p f hf) W (V 0) (V 1) ∧
    W ≤ V 0 ⊔ V 1 ⊔ V 2
  pair_short : ∃ W, LinearBlockStandardPair (GaloisField p (2 * f)) W (V 1) (V 2)
  cover : ∀ L ∈ centralizingMembers Ω {z}, L ≠ K → ∃ h ∈ V 0 ⊔ V 1 ⊔ V 2, L = conjSub h (V 0)

@[expose] def TE6Partner (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (V : Fin 3 → Subgroup G) : Prop :=
  ∃ β ∈ Ω, (∃ W, LinearBlockStandardPair (GaloisField p f) W β (V 0)) ∧ Commutes β (V 1) ∧
    Commutes β (V 2)

theorem IsTE6Base.isTE6Chain {hf : 1 ≤ f} {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}
    {V : Fin 3 → Subgroup G} (hV : IsTE6Base p f hf Ω K z V) {β : Subgroup G}
    (h01 : ∃ W, LinearBlockStandardPair (GaloisField p f) W β (V 0)) (h1 : Commutes β (V 1))
    (h2 : Commutes β (V 2)) : IsTE6Chain p f hf ![β, V 0, V 1, V 2] where
  comm i j hij := by
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · exact h1
    · exact h2
    · exact hV.comm
  pair01 := h01
  pair23 := hV.pair_short
  pair12 := hV.pair_long

theorem routeD_twistedE6_of_base [Finite G] (hadm : StatedLieAdmissible .twistedE6 0 p f)
    (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) {V : Fin 3 → Subgroup G}
    (hV : IsTE6Base p f hadm.2.1 Ω K z V) (hpartner : TE6Partner p f Ω V) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .twistedE6 ∧ D.rank i = 0 := by
  obtain ⟨β, hβ, h01, h1, h2⟩ := hpartner
  exact routeD_twistedE6_of_chain hadm hq hΩ hK hsingle hconn hz
    (U := ![β, V 0, V 1, V 2]) (hV.isTE6Chain h01 h1 h2) hβ hV.cover

section Existence

theorem injective_comp_of_center {X Y Z W : Type*} [Group X] [Group Y] [Group Z] [Group W]
    (Θ : Y →* Z) (hker : Θ.ker ≤ Subgroup.center Y) (ι : X →* Y) (b : W →* X)
    (hb : Function.Injective (ι.comp b)) (S : Subgroup Y) (hS : (ι.comp b).range ≤ S)
    (hSc : ∀ s ∈ S, s ∈ Subgroup.center Y → s = 1) : Function.Injective ((Θ.comp ι).comp b) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 : (ι.comp b) a ∈ Θ.ker := ha
  have h2 : (ι.comp b) a = 1 := hSc _ (hS ⟨a, rfl⟩) (hker h1)
  exact (injective_iff_map_eq_one _).mp hb a h2

theorem ker_comp_le_center {X Y Z : Type*} [Group X] [Group Y] [Group Z] (Θ : Y →* Z)
    (hker : Θ.ker ≤ Subgroup.center Y) (ι : X →* Y) (hι : Function.Injective ι) :
    (Θ.comp ι).ker ≤ Subgroup.center X := by
  intro x hx
  have hc := hker (show ι x ∈ Θ.ker from hx)
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro y
  apply hι
  rw [map_mul, map_mul]
  exact hc (ι y)

variable [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem UCtx.exists_te6Base (c : UCtx p f 5 Ω K z) (nd : UNodes c) (hf : 1 ≤ f)
    (F : SU6Frame p f hf) : ∃ V : Fin 3 → Subgroup G, IsTE6Base p f hf Ω K z V := by
  classical
  have hiso : ∀ i : Fin (3 + 2), Nonempty (Su (GaloisField p (2 * f)) p f 2 ≃* ↥(nd.j i.val)) :=
    fun i => nonempty_su_two_equiv_of_member c.hq c.hΩ c.hex
      (nd.mem i.val (by have := i.isLt; omega)).1
  have hcomm : ∀ i j : Fin (3 + 2), (i : ℕ) + 1 < j → Commutes (nd.j i.val) (nd.j j.val) :=
    fun i j hij => nd.far i.val (by omega) j.val (by omega) (by omega)
  have hpair : ∀ i j : Fin (3 + 2), (j : ℕ) = i + 1 → ∃ W, UnitaryBlockStandardPair
      (GaloisField p (2 * f)) p f W (nd.j i.val) (nd.j j.val) := by
    intro i j hij
    have := nd.pair i.val (by omega)
    rwa [← hij] at this
  obtain ⟨Θ, hker, hrange, hblk⟩ : ∃ Θ : Su (GaloisField p (2 * f)) p f 6 →* G,
      Θ.ker ≤ Subgroup.center _ ∧ Θ.range = ⨆ i : Fin 5, nd.j i.val ∧
      ∀ i : Fin 5, (blockEmb2 (GaloisField p (2 * f)) p f 5 i).range.map Θ = nd.j i.val :=
    exists_psi_of_chainU c.hq (m := 3) (by norm_num) (U := fun i : Fin (3 + 2) => nd.j i.val)
      hiso hcomm hpair
  have hn6 : 2 ≤ 6 := by norm_num
  set T : Set (Subgroup (Su (GaloisField p (2 * f)) p f 6)) :=
    longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) hn6 with hT
  have h0 : (rootSU2 (GaloisField p (2 * f)) p f hn6).map Θ = nd.j 0 := hblk ⟨0, by norm_num⟩
  have hconj : ∀ R ∈ T, ∃ g, R.map Θ = conjSub (Θ g) (nd.j 0) := by
    intro R hR
    obtain ⟨g, hg⟩ := (mem_longRootSetU_iff hn6).mp hR
    refine ⟨g, ?_⟩
    rw [hg, ← h0, conjSub_map]
    rfl
  have hmemΩ : ∀ R ∈ T, R.map Θ ∈ Ω := by
    intro R hR
    obtain ⟨g, hg⟩ := hconj R hR
    rw [hg]
    exact c.hΩ.conjInvariant _ _ (nd.mem 0 (by norm_num)).1
  have hRange_cz : Θ.range ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [hrange]
    exact iSup_le fun i => (nd.mem i.val (by omega)).2
  have hKc : Commutes K Θ.range := by
    have : Θ.range ≤ Subgroup.centralizer (K : Set G) := by
      rw [hrange]
      refine iSup_le fun i x hx => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact nd.commK i.val (by omega) k hk x hx
    intro k hk x hx
    exact (Subgroup.mem_centralizer_iff.mp (this hx)) k hk
  set B : Set (Subgroup G) := centralizingMembers Ω {z} \ {K} with hB
  set A : Set (Subgroup G) := (fun R => R.map Θ) '' T with hA
  have hAB : A ⊆ B := by
    rintro _ ⟨R, hR, rfl⟩
    refine ⟨⟨hmemΩ R hR, (Subgroup.map_le_range Θ R).trans hRange_cz⟩, fun hRK => ?_⟩
    have hRK' : R.map Θ = K := hRK
    refine not_commutes_self_of_mem c.hΩ c.hK ?_
    intro k hk k' hk'
    rw [← hRK'] at hk'
    exact hKc k hk k' (Subgroup.map_le_range Θ R hk')
  have hperf : ∀ R ∈ T, R ≤ ⁅R, R⁆ := by
    rintro R ⟨i, hi⟩
    exact (Subgroup.isPerfect_iff.mp (c.isPerfect_of_isLongRootSU2 hi)).ge
  have hinj : Set.InjOn (fun R => R.map Θ) T := fun R hR R' hR' h =>
    eq_of_map_eq_of_perfect Θ hker (hperf R hR) (hperf R' hR') h
  have hBle : B.ncard ≤ T.ncard := by
    set T' : Set (Subgroup (locQuot Ω z)) := (fun R => R.map c.d.ψ) '' T with hT'
    have h1 : ∀ L ∈ B, locImg Ω z L ∈ T' := by
      rintro L ⟨hL, hLK⟩
      obtain ⟨R, hR, hLR⟩ := typeU_exists_root_of_ne c.hp2 c.hq c.hm c.hΩ c.hex c.hK c.hz c.hP1
        c.d hL hLK
      exact ⟨R, hR, hLR.symm⟩
    have h2 : Set.InjOn (fun L => locImg Ω z L) B := fun L hL L' hL' h =>
      locImg_injOn c.hΩ c.hP1 hL.1 hL'.1 h
    calc B.ncard ≤ T'.ncard := Set.ncard_le_ncard_of_injOn _ h1 h2 (Set.toFinite _)
      _ ≤ T.ncard := Set.ncard_image_le (Set.toFinite _)
  have hAeq : A = B := by
    refine Set.eq_of_subset_of_ncard_le hAB ?_ (Set.toFinite _)
    rw [hA, hinj.ncard_image]
    exact hBle
  have hgenV : F.R₁.map Θ ⊔ F.S₂.map Θ ⊔ F.S₃.map Θ = Θ.range := by
    rw [← Subgroup.map_sup, ← Subgroup.map_sup, F.gen, Subgroup.map_top]
  refine ⟨![F.R₁.map Θ, F.S₂.map Θ, F.S₃.map Θ], ?_, ?_, ?_, ?_, ?_⟩
  · exact hmemΩ F.R₁ F.R₁_mem
  · exact commutes_map Θ F.commutes_R₁_S₃
  · refine ⟨(Θ.comp F.ι₄).range, ?_, ?_⟩
    · refine ⟨Θ.comp F.ι₄, rfl, ker_comp_le_center Θ hker F.ι₄ F.ι₄_injective, ?_, ?_, ?_, ?_⟩
      · refine injective_comp_of_center Θ hker F.ι₄ (unitaryModel (frobQ p f)
          (frobQ_frobQ p f hf)).lb (F.ι₄_injective.comp (ulb_injective _ _)) F.R₁ ?_ F.R₁_center
        rw [MonoidHom.range_comp, F.ι₄_long]
      · refine injective_comp_of_center Θ hker F.ι₄ (unitaryModel (frobQ p f)
          (frobQ_frobQ p f hf)).sb (F.ι₄_injective.comp (usb_injective _ _)) F.S₂ ?_ F.S₂_center
        rw [MonoidHom.range_comp, F.ι₄_short]
      · rw [← Subgroup.map_map, F.ι₄_long]
        rfl
      · rw [← Subgroup.map_map, F.ι₄_short]
        rfl
    · show (Θ.comp F.ι₄).range ≤ F.R₁.map Θ ⊔ F.S₂.map Θ ⊔ F.S₃.map Θ
      rw [hgenV]
      rintro _ ⟨x, rfl⟩
      exact ⟨F.ι₄ x, rfl⟩
  · refine ⟨(Θ.comp F.ι₃).range, Θ.comp F.ι₃, 1, rfl,
      ker_comp_le_center Θ hker F.ι₃ F.ι₃_injective, Or.inr ⟨?_, ?_⟩⟩
    · have e : (MulAut.conj (1 : SL(3, GaloisField p (2 * f)))⁻¹).toMonoidHom = MonoidHom.id _ := by
        ext x
        simp
      rw [e, Subgroup.map_id, ← Subgroup.map_map, F.ι₃_B12]
      rfl
    · have e : (MulAut.conj (1 : SL(3, GaloisField p (2 * f)))⁻¹).toMonoidHom = MonoidHom.id _ := by
        ext x
        simp
      rw [e, Subgroup.map_id, ← Subgroup.map_map, F.ι₃_B23]
      rfl
  · intro L hL hLK
    have hLB : L ∈ B := ⟨hL, hLK⟩
    rw [← hAeq] at hLB
    obtain ⟨R, hR, rfl⟩ := hLB
    obtain ⟨i, hi⟩ := hR
    obtain ⟨i₁, hi₁⟩ := F.R₁_mem
    obtain ⟨g, hg⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_conj_of_isLongRootSU2 hi hi₁
    refine ⟨Θ g, ?_, ?_⟩
    · show Θ g ∈ F.R₁.map Θ ⊔ F.S₂.map Θ ⊔ F.S₃.map Θ
      rw [hgenV]
      exact ⟨g, rfl⟩
    · show R.map Θ = conjSub (Θ g) (F.R₁.map Θ)
      rw [hg, conjSub_map]
      rfl

end Existence

end CFSG.ClassicalInvolution.RouteD
