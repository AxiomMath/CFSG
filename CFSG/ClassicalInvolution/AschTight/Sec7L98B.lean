module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen610
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen611
public import CFSG.ClassicalInvolution.AschTight.Sec7L713F

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

theorem conj_eq_of_mem_centralizer {g z : G} (hg : g ∈ Subgroup.centralizer ({z} : Set G)) :
    g * z * g⁻¹ = z := by
  have h := Subgroup.mem_centralizer_singleton_iff.mp hg
  calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [h]
    _ = z := by group

theorem conjSub_iSup_le {η : Set (Subgroup G)} {g : G} (h : ∀ U ∈ η, conjSub g U ∈ η) :
    conjSub g (⨆ U ∈ η, U) ≤ ⨆ U ∈ η, U := by
  change (⨆ U ∈ η, U).map (MulAut.conj g).toMonoidHom ≤ _
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun U hU => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_iSup₂ (f := fun V (_ : V ∈ η) => V) (conjSub g U) (h U hU)

theorem conjSub_sup_eq (g : G) (A B : Subgroup G) :
    conjSub g (A ⊔ B) = conjSub g A ⊔ conjSub g B :=
  Subgroup.map_sup _ _ _

theorem le_normalizer_of_conjSub_le {A H : Subgroup G} (h : ∀ g ∈ H, conjSub g A ≤ A) :
    H ≤ Subgroup.normalizer (A : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_conjSub_eq]
  refine le_antisymm (h g hg) ?_
  have h2 := conjSub_mono (n := g) (h g⁻¹ (H.inv_mem hg))
  rwa [conjSub_conjSub_inv] at h2

structure Cfg98 (Ω : Set (Subgroup G)) (K J K' X P : Subgroup G) (z j : G) (S : Sylow 2 G)
    (W : Subgroup G) : Prop where
  hΩ : HypOmegaGen Ω
  hK : K ∈ Ω
  hJ : J ∈ Ω
  hA : InA Ω K J
  hz : IsUniqueInvolution K z
  hj : IsUniqueInvolution J j
  hK' : K' ∈ Ω
  hne : K' ≠ K
  htw : twinSet Ω K = {K, K'}
  hX2 : IsPGroup 2 X
  hXc : X ≤ Subgroup.centralizer ({z, j} : Set G)
  hP : IsSylow2In P ((K ⊔ K') ⊔ (J ⊓ Subgroup.centralizer ({z} : Set G)))
  hXP : ∀ x ∈ X, conjSub x P = P
  hPS : P ⊔ X ≤ (S : Subgroup G)
  hJS : 2 < Nat.card ↥(J ⊓ (S : Subgroup G))
  hW : W ∈ WSet Ω
  hWS : W ≤ (S : Subgroup G)

namespace Cfg98

variable {Ω : Set (Subgroup G)} {K J K' X P : Subgroup G} {z j : G} {S : Sylow 2 G}
  {W : Subgroup G} (c : Cfg98 Ω K J K' X P z j S W)
include c

theorem hzK' : IsUniqueInvolution K' z := by
  have hK'tw : K' ∈ twinSet Ω K := by rw [c.htw]; exact Or.inr rfl
  obtain ⟨-, z', hz'K, hz'K'⟩ := hK'tw
  rw [c.hz.eq hz'K]
  exact hz'K'

theorem hJne : J ≠ K := c.hA.1.2.1

theorem K'_le [Finite G] : K' ≤ Subgroup.normalizer (K : Set G) :=
  Sec6Gen.le_normalizer_of_twin c.hΩ c.hK' c.hK c.hne c.hzK' c.hz

theorem K_le [Finite G] : K ≤ Subgroup.normalizer (K' : Set G) :=
  Sec6Gen.le_normalizer_of_twin c.hΩ c.hK c.hK' c.hne.symm c.hz c.hzK'

theorem z_ne_j [Finite G] : z ≠ j := by
  intro hzj
  have hJtw : J ∈ twinSet Ω K := ⟨c.hJ, z, c.hz, hzj ▸ c.hj⟩
  rw [c.htw] at hJtw
  rcases hJtw with h | h
  · exact c.hJne h
  · apply c.hA.2.1
    obtain ⟨R, hR⟩ := exists_isSylow2In K'
    have hJK' : J = K' := h
    refine ⟨c.hJ, c.hJne, R, mem_RSet_of_isSylow2In c.hK' hR, hJK' ▸ hR.1, ?_⟩
    exact hR.1.trans c.K'_le

theorem conj_K_of_cent {g : G} (hg : g ∈ Subgroup.centralizer ({z} : Set G)) :
    conjSub g K = K ∨ conjSub g K = K' := by
  have h1 : conjSub g K ∈ twinSet Ω K :=
    ⟨c.hΩ.conjInvariant g K c.hK, z, c.hz, conj_eq_of_mem_centralizer hg ▸ c.hz.conj g⟩
  rw [c.htw] at h1
  exact h1

theorem conj_K'_of_cent {g : G} (hg : g ∈ Subgroup.centralizer ({z} : Set G)) :
    conjSub g K' = K ∨ conjSub g K' = K' := by
  have h1 : conjSub g K' ∈ twinSet Ω K :=
    ⟨c.hΩ.conjInvariant g K' c.hK', z, c.hz, conj_eq_of_mem_centralizer hg ▸ c.hzK'.conj g⟩
  rw [c.htw] at h1
  exact h1

theorem conj_K_iff {g : G} (hg : g ∈ Subgroup.centralizer ({z} : Set G)) :
    conjSub g K = K ↔ conjSub g K' = K' := by
  constructor
  · intro h
    rcases c.conj_K'_of_cent hg with h' | h'
    · exact absurd (conjSub_injective g (h'.trans h.symm)) c.hne
    · exact h'
  · intro h
    rcases c.conj_K_of_cent hg with h' | h'
    · exact h'
    · exact absurd (conjSub_injective g (h.trans h'.symm)) c.hne

theorem cent_le_normalizer_sup :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_conjSub_eq]
  change (K ⊔ K').map (MulAut.conj g).toMonoidHom = K ⊔ K'
  rw [Subgroup.map_sup]
  change conjSub g K ⊔ conjSub g K' = K ⊔ K'
  rcases c.conj_K_of_cent hg with h | h
  · rw [h, (c.conj_K_iff hg).mp h]
  · rcases c.conj_K'_of_cent hg with h' | h'
    · rw [h, h', sup_comm]
    · exact absurd (conjSub_injective g (h.trans h'.symm)) c.hne.symm

theorem H0_le_normalizer :
    (K ⊔ K') ⊔ (J ⊓ Subgroup.centralizer ({z} : Set G)) ≤
      Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) :=
  sup_le Subgroup.le_normalizer (inf_le_right.trans c.cent_le_normalizer_sup)

theorem le_P {A : Subgroup G} (hA : A ≤ (K ⊔ K') ⊔ (J ⊓ Subgroup.centralizer ({z} : Set G)))
    (hAS : A ≤ (S : Subgroup G)) : A ≤ P := by
  have h2 : IsPGroup 2 ↥(P ⊔ A) := S.isPGroup'.to_le (sup_le (le_sup_left.trans c.hPS) hAS)
  have h := c.hP.eq_of_le h2 (sup_le c.hP.1 hA) le_sup_left
  rw [← h]
  exact le_sup_right

theorem sylow_R [Finite G] : IsSylow2In (K ⊓ (S : Subgroup G)) K := by
  have h1 := isSylow2In_inf_of_normal c.hP le_sup_left c.H0_le_normalizer
  have hKN : K ⊔ K' ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer c.K'_le
  have h2 := isSylow2In_inf_of_normal h1 le_sup_left hKN
  have hle : (P ⊓ (K ⊔ K')) ⊓ K ≤ K ⊓ (S : Subgroup G) :=
    le_inf inf_le_right (inf_le_left.trans (inf_le_left.trans (le_sup_left.trans c.hPS)))
  have h3 := h2.eq_of_le (S.isPGroup'.to_le inf_le_right) inf_le_left hle
  rw [h3]
  exact h2

theorem sylow_R' [Finite G] : IsSylow2In (K' ⊓ (S : Subgroup G)) K' := by
  have h1 := isSylow2In_inf_of_normal c.hP le_sup_left c.H0_le_normalizer
  have hKN : K ⊔ K' ≤ Subgroup.normalizer (K' : Set G) := sup_le c.K_le Subgroup.le_normalizer
  have h2 := isSylow2In_inf_of_normal h1 le_sup_right hKN
  have hle : (P ⊓ (K ⊔ K')) ⊓ K' ≤ K' ⊓ (S : Subgroup G) :=
    le_inf inf_le_right (inf_le_left.trans (inf_le_left.trans (le_sup_left.trans c.hPS)))
  have h3 := h2.eq_of_le (S.isPGroup'.to_le inf_le_right) inf_le_left hle
  rw [h3]
  exact h2

theorem W_abelian [Finite G] : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
  obtain ⟨η, ⟨S', hηS', hinv⟩, rfl⟩ := c.hW
  exact (Sec6Gen.eta_abelian_of_cyc66 c.hΩ (Sec6Gen.cyc66 c.hΩ) hηS' hinv).1

theorem W_isPGroup : IsPGroup 2 W := S.isPGroup'.to_le c.hWS

theorem inf_W_mem [Finite G] {M : Subgroup G} (hM : M ∈ Ω)
    (h2 : 2 < Nat.card ↥(M ⊓ (S : Subgroup G))) : M ⊓ W ∈ USet Ω := by
  obtain ⟨η, hη, rfl⟩ := c.hW
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV =>
    (le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV).trans c.hWS
  have h := Sec6Gen.l6_11Gen G Ω c.hΩ S η hη hηS M hM h2
  obtain ⟨S', hηS', -⟩ := hη
  exact (hηS'.1 h).1

theorem two_lt_K [Finite G] : 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) := by
  have := Sec6Gen.eight_le_of_mem_RSet c.hΩ (mem_RSet_of_isSylow2In c.hK c.sylow_R)
  omega

theorem two_lt_K' [Finite G] : 2 < Nat.card ↥(K' ⊓ (S : Subgroup G)) := by
  have := Sec6Gen.eight_le_of_mem_RSet c.hΩ (mem_RSet_of_isSylow2In c.hK' c.sylow_R')
  omega

theorem z_mem_W [Finite G] : z ∈ K ⊓ W :=
  c.hz.mem_of_le inf_le_left (Sec6Gen.isPGroup_of_mem_USet c.hΩ (c.inf_W_mem c.hK c.two_lt_K))
    (by
      obtain ⟨-, -, -, -, -, -, -, -, h4⟩ :=
        Sec6Gen.exists_data_of_mem_USet c.hΩ (c.inf_W_mem c.hK c.two_lt_K)
      omega)

theorem j_mem_W [Finite G] : j ∈ J ⊓ W :=
  c.hj.mem_of_le inf_le_left (Sec6Gen.isPGroup_of_mem_USet c.hΩ (c.inf_W_mem c.hJ c.hJS))
    (by
      obtain ⟨-, -, -, -, -, -, -, -, h4⟩ :=
        Sec6Gen.exists_data_of_mem_USet c.hΩ (c.inf_W_mem c.hJ c.hJS)
      omega)

theorem W_le_centralizer [Finite G] {w : G} (hw : w ∈ W) :
    W ≤ Subgroup.centralizer ({w} : Set G) := fun x hx =>
  Subgroup.mem_centralizer_singleton_iff.mpr (c.W_abelian w hw x hx).symm

theorem J_ne_K' [Finite G] : J ≠ K' := by
  intro h
  apply c.z_ne_j
  have h1 : IsUniqueInvolution J z := h ▸ c.hzK'
  exact h1.eq c.hj

theorem V_le_N_K [Finite G] : J ⊓ W ≤ Subgroup.normalizer (K : Set G) := by
  have hV := c.inf_W_mem c.hJ c.hJS
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet c.hΩ hV
  exact Sec6Gen.le_normalizer_of_le_centralizer c.hΩ c.hK c.hJ c.hJne.symm c.hz inf_le_left
    (Sec6Gen.isPGroup_of_mem_USet c.hΩ hV) (by omega)
    (inf_le_right.trans (c.W_le_centralizer (Subgroup.mem_inf.mp c.z_mem_W).2))

theorem V_le_N_K' [Finite G] : J ⊓ W ≤ Subgroup.normalizer (K' : Set G) := by
  have hV := c.inf_W_mem c.hJ c.hJS
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet c.hΩ hV
  exact Sec6Gen.le_normalizer_of_le_centralizer c.hΩ c.hK' c.hJ c.J_ne_K'.symm c.hzK' inf_le_left
    (Sec6Gen.isPGroup_of_mem_USet c.hΩ hV) (by omega)
    (inf_le_right.trans (c.W_le_centralizer (Subgroup.mem_inf.mp c.z_mem_W).2))

theorem W_le_N_J [Finite G] : W ≤ Subgroup.normalizer (J : Set G) := by
  have hjW := (Subgroup.mem_inf.mp c.j_mem_W).2
  have hWS := c.hWS
  have hWab := c.W_abelian
  obtain ⟨η, hη, rfl⟩ := c.hW
  obtain ⟨S', hηS', -⟩ := id hη
  refine iSup₂_le fun U hU => ?_
  have hUU : U ∈ USet Ω := (hηS'.1 hU).1
  obtain ⟨M, hM, hUM⟩ := Sec6Gen.exists_member_of_mem_USet c.hΩ hUU
  by_cases hMJ : M = J
  · exact (hMJ ▸ hUM).trans Subgroup.le_normalizer
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet c.hΩ hUU
  have hUW : U ≤ ⨆ V ∈ η, V := le_iSup₂ (f := fun V (_ : V ∈ η) => V) U hU
  refine Sec6Gen.le_normalizer_of_le_centralizer c.hΩ c.hJ hM (Ne.symm hMJ) c.hj hUM
    (Sec6Gen.isPGroup_of_mem_USet c.hΩ hUU) (by omega) ?_
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mpr (hWab j hjW x (hUW hx)).symm

theorem le_normalizer_W [Finite G] {S₂ : Sylow 2 G} (hWS₂ : W ≤ (S₂ : Subgroup G))
    {R : Subgroup G} (hR : R ∈ RSet Ω) (hRS₂ : R ≤ (S₂ : Subgroup G)) :
    R ≤ Subgroup.normalizer (W : Set G) := by
  obtain ⟨η, hη, rfl⟩ := c.hW
  have hηS : ∀ V ∈ η, V ≤ (S₂ : Subgroup G) := fun V hV =>
    (le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV).trans hWS₂
  have h610 := (Sec6Gen.l6_10Gen G Ω c.hΩ S₂ η hη hηS).1 R hR hRS₂
  intro r hr
  rw [mem_normalizer_iff_conjSub_eq]
  refine le_antisymm (conjSub_iSup_le (h610 r hr)) ?_
  have h1 := conjSub_iSup_le (h610 r⁻¹ (R.inv_mem hr))
  have h2 := conjSub_mono (n := r) h1
  rwa [conjSub_conjSub_inv] at h2

theorem R_le_N_UV [Finite G] {u v : G} (hu : Subgroup.zpowers u = K ⊓ W)
    (hv : Subgroup.zpowers v = J ⊓ W) :
    K ⊓ (S : Subgroup G) ≤
      Subgroup.normalizer ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) := by
  have hRW : K ⊓ (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) :=
    c.le_normalizer_W c.hWS (mem_RSet_of_isSylow2In c.hK c.sylow_R) inf_le_right
  have huKW : u ∈ K ⊓ W := hu ▸ Subgroup.mem_zpowers u
  have hvJW : v ∈ J ⊓ W := hv ▸ Subgroup.mem_zpowers v
  have hvR : v ∈ Subgroup.normalizer ((K ⊓ (S : Subgroup G) : Subgroup G) : Set G) :=
    mem_normalizer_inf (c.V_le_N_K hvJW) (Subgroup.le_normalizer (c.hWS hvJW.2))
  refine le_normalizer_of_conjSub_le fun r hr => ?_
  rw [conjSub_sup_eq, AscL62.conjSub_zpowers_eq, AscL62.conjSub_zpowers_eq]
  refine sup_le ?_ ?_
  · rw [Subgroup.zpowers_le]
    apply Subgroup.mem_sup_left
    rw [hu]
    exact ⟨K.mul_mem (K.mul_mem hr.1 huKW.1) (K.inv_mem hr.1),
      (Subgroup.mem_normalizer_iff.mp (hRW hr) u).mp huKW.2⟩
  · rw [Subgroup.zpowers_le]
    have h1 : r * v * r⁻¹ * v⁻¹ ∈ K ⊓ (S : Subgroup G) := by
      have h0 : v * r⁻¹ * v⁻¹ ∈ K ⊓ (S : Subgroup G) :=
        (Subgroup.mem_normalizer_iff.mp hvR r⁻¹).mp (Subgroup.inv_mem _ hr)
      rw [show r * v * r⁻¹ * v⁻¹ = r * (v * r⁻¹ * v⁻¹) by group]
      exact Subgroup.mul_mem _ hr h0
    have h2 : r * v * r⁻¹ * v⁻¹ ∈ W :=
      W.mul_mem ((Subgroup.mem_normalizer_iff.mp (hRW hr) v).mp hvJW.2) (W.inv_mem hvJW.2)
    have h3 : r * v * r⁻¹ * v⁻¹ ∈ Subgroup.zpowers u := by
      rw [hu]
      exact ⟨(Subgroup.mem_inf.mp h1).1, h2⟩
    rw [show r * v * r⁻¹ = (r * v * r⁻¹ * v⁻¹) * v by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h3)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))

theorem exists_T [Finite G] {u v : G} (hu : Subgroup.zpowers u = K ⊓ W)
    (hv : Subgroup.zpowers v = J ⊓ W) :
    ∃ T : Subgroup G, IsSylow2In T J ∧ Subgroup.zpowers v ≤ T ∧
      T ≤ Subgroup.normalizer ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) := by
  have hWJ : W ⊔ J ≤ Subgroup.normalizer (J : Set G) := sup_le c.W_le_N_J Subgroup.le_normalizer
  obtain ⟨Q₂, hQ₂, hWQ₂⟩ := IsSylow2In.exists_ge c.W_isPGroup (le_sup_left : W ≤ W ⊔ J)
  have hT := isSylow2In_inf_of_normal hQ₂ le_sup_right hWJ
  obtain ⟨S₂, hS₂⟩ := hQ₂.2.1.exists_le_sylow
  have hTW : Q₂ ⊓ J ≤ Subgroup.normalizer (W : Set G) :=
    c.le_normalizer_W (hWQ₂.trans hS₂) (mem_RSet_of_isSylow2In c.hJ hT) (inf_le_left.trans hS₂)
  have hQ₂N : Q₂ ≤ Subgroup.normalizer ((Q₂ ⊓ J : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_inf (Subgroup.le_normalizer hg) (hWJ (hQ₂.1 hg))
  have huKW : u ∈ K ⊓ W := hu ▸ Subgroup.mem_zpowers u
  have hvJW : v ∈ J ⊓ W := hv ▸ Subgroup.mem_zpowers v
  refine ⟨Q₂ ⊓ J, hT, ?_, le_normalizer_of_conjSub_le fun t ht => ?_⟩
  · rw [hv]
    exact le_inf (inf_le_right.trans hWQ₂) inf_le_left
  rw [conjSub_sup_eq, AscL62.conjSub_zpowers_eq, AscL62.conjSub_zpowers_eq]
  refine sup_le ?_ ?_
  · rw [Subgroup.zpowers_le]
    have huQ : u ∈ Q₂ := hWQ₂ huKW.2
    have h1 : t * u * t⁻¹ * u⁻¹ ∈ Q₂ ⊓ J := by
      have h0 : u * t⁻¹ * u⁻¹ ∈ Q₂ ⊓ J :=
        (Subgroup.mem_normalizer_iff.mp (hQ₂N huQ) t⁻¹).mp (Subgroup.inv_mem _ ht)
      rw [show t * u * t⁻¹ * u⁻¹ = t * (u * t⁻¹ * u⁻¹) by group]
      exact Subgroup.mul_mem _ ht h0
    have h2 : t * u * t⁻¹ * u⁻¹ ∈ W :=
      W.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTW ht) u).mp huKW.2) (W.inv_mem huKW.2)
    have h3 : t * u * t⁻¹ * u⁻¹ ∈ Subgroup.zpowers v := by
      rw [hv]
      exact ⟨(Subgroup.mem_inf.mp h1).2, h2⟩
    rw [show t * u * t⁻¹ = (t * u * t⁻¹ * u⁻¹) * u by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h3)
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))
  · rw [Subgroup.zpowers_le]
    apply Subgroup.mem_sup_right
    rw [hv]
    exact ⟨J.mul_mem (J.mul_mem (Subgroup.mem_inf.mp ht).2 hvJW.1)
      (J.inv_mem (Subgroup.mem_inf.mp ht).2), (Subgroup.mem_normalizer_iff.mp (hTW ht) v).mp hvJW.2⟩

end Cfg98

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
