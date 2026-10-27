module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526Defs
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15TILemma
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511A
import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open scoped commutatorElement

section Row26X

variable {X : Type} [Group X] [Finite X]

theorem commutator_gnV_sup_gnC (T L : Subgroup X) : ⁅gnV T, L ⊔ gnC T⁆ = ⁅L, gnV T⁆ := by
  apply le_antisymm
  · rw [Subgroup.commutator_comm L (gnV T)]
    rw [Subgroup.commutator_le]
    intro v hv g hg
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hg
    have hzv : z * v⁻¹ = v⁻¹ * z := by
      have := (Subgroup.mem_centralizer_iff.1 hz) v⁻¹ (Subgroup.inv_mem _ hv)
      exact this.symm
    have : ⁅v, y * z⁆ = ⁅v, y⁆ := by
      simp only [commutatorElement_def]
      calc v * (y * z) * v⁻¹ * (y * z)⁻¹ = v * y * (z * v⁻¹) * z⁻¹ * y⁻¹ := by group
        _ = v * y * (v⁻¹ * z) * z⁻¹ * y⁻¹ := by rw [hzv]
        _ = v * y * v⁻¹ * y⁻¹ := by group
    rw [this]
    exact Subgroup.commutator_mem_commutator hv hy
  · rw [Subgroup.commutator_comm L (gnV T)]
    exact Subgroup.commutator_mono le_rfl le_sup_left

theorem commutator_gnV_le (T L : Subgroup X) : ⁅gnV T, L⁆ ≤ gnV T := by
  rw [Subgroup.commutator_le]
  intro v hv l hl
  have hn : (gnV T).Normal := Subgroup.normalClosure_normal
  have h1 := hn.conj_mem v⁻¹ (Subgroup.inv_mem _ hv) l
  have h2 : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by simp only [commutatorElement_def]; group
  rw [h2]
  exact Subgroup.mul_mem _ hv h1

theorem relIndex_sup_of_le_normal {H L C : Subgroup X} [C.Normal] (hC : C ≤ H) :
    H.relIndex (L ⊔ C) = H.relIndex L := by
  have hprod : ∀ A : Subgroup X, Nat.card ↥(A ⊔ C) * Nat.card ↥(A ⊓ C) = Nat.card ↥A * Nat.card ↥C := by
    intro A
    have h1 := CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal C A
    have h2 := Subgroup.relIndex_mul_card A (C ⊔ A)
    have h3 := Subgroup.relIndex_mul_card C A
    have h4 := Subgroup.relIndex_mul_card A C
    rw [inf_eq_left.mpr (le_sup_right : A ≤ C ⊔ A), h1] at h2
    rw [sup_comm] at h2
    calc Nat.card ↥(A ⊔ C) * Nat.card ↥(A ⊓ C)
        = (A.relIndex C * Nat.card ↥A) * Nat.card ↥(A ⊓ C) := by rw [h2]
      _ = Nat.card ↥A * (A.relIndex C * Nat.card ↥(A ⊓ C)) := by ring
      _ = Nat.card ↥A * Nat.card ↥C := by rw [h4]
  have hmod : H ⊓ (L ⊔ C) = (H ⊓ L) ⊔ C := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxH, hxLC⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨l, hl, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hxLC
      have hlH : l ∈ H := by
        have := H.mul_mem hxH (H.inv_mem (hC hc))
        simpa using this
      exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hlH, hl⟩) hc
    · exact sup_le (inf_le_inf_left _ le_sup_left) (le_inf hC le_sup_right)
  have hinf : (H ⊓ L) ⊓ C = L ⊓ C := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h2, h3⟩
    · rintro ⟨h2, h3⟩; exact ⟨⟨hC h3, h2⟩, h3⟩
  have e1 := Subgroup.relIndex_mul_card H (L ⊔ C)
  have e2 := Subgroup.relIndex_mul_card H L
  have p1 := hprod L
  have p2 := hprod (H ⊓ L)
  rw [hinf] at p2
  rw [← hmod] at p2
  have hpos : 0 < Nat.card ↥(L ⊓ C) := Nat.card_pos
  have hposC : 0 < Nat.card ↥C := Nat.card_pos
  have hposHL : 0 < Nat.card ↥(H ⊓ L) := Nat.card_pos
  have hposHLC : 0 < Nat.card ↥(H ⊓ (L ⊔ C)) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hposHLC hpos)
  calc H.relIndex (L ⊔ C) * (Nat.card ↥(H ⊓ (L ⊔ C)) * Nat.card ↥(L ⊓ C))
      = Nat.card ↥(L ⊔ C) * Nat.card ↥(L ⊓ C) := by rw [← e1]; ring
    _ = Nat.card ↥L * Nat.card ↥C := p1
    _ = (H.relIndex L * Nat.card ↥(H ⊓ L)) * Nat.card ↥C := by rw [e2]
    _ = H.relIndex L * (Nat.card ↥(H ⊓ L) * Nat.card ↥C) := by ring
    _ = H.relIndex L * (Nat.card ↥(H ⊓ (L ⊔ C)) * Nat.card ↥(L ⊓ C)) := by rw [p2]

theorem isNaturalLThreeTwo_of_sup {L C N : Subgroup X} [C.Normal]
    (hC : C ≤ Subgroup.centralizer (N : Set X)) (h : IsNaturalLThreeTwo (L ⊔ C) N) :
    IsNaturalLThreeTwo L N := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, le_sup_left.trans h3, ?_⟩
  rw [← relIndex_sup_of_le_normal (L := L) hC]
  exact h4

theorem isNatSum_of_K55 (hK55 : K55) {T : Subgroup X} (hX : GNSetting X T)
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hLs : IsComponentOf Ls ⊤)
    (hJ : ⁅Ls, gnImg T (CFSG.Quasithin.thompsonJ T)⁆ = Ls) (hL3 : IsLThreeOfExp 1 ↥Ls)
    (hL : LiftOf T L Ls) : IsNatSum L ⁅L, gnV T⁆ := by
  obtain ⟨N₁, N₂, h1, h2, h3⟩ := hK55 X T hX Ls hLs hJ hL3
  have hc : Ls.comap (toStar T) = L ⊔ gnC T := (liftOf_central_ext hX hLs hL).2
  rw [hc] at h1 h2 h3
  rw [commutator_gnV_sup_gnC] at h2
  have hle : ⁅L, gnV T⁆ ≤ gnV T := by
    rw [Subgroup.commutator_comm]; exact commutator_gnV_le T L
  have hN1 : gnC T ≤ Subgroup.centralizer (N₁ : Set X) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (le_sup_left.trans (h2.le.trans hle)))
  refine ⟨N₁, N₂, isNaturalLThreeTwo_of_sup hN1 h1, h2, ?_⟩
  rcases h3 with h3 | ⟨h3a, h3b, f, hf⟩
  · exact Or.inl h3
  · have hN2 : gnC T ≤ Subgroup.centralizer (N₂ : Set X) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (le_sup_right.trans (h2.le.trans hle)))
    exact Or.inr ⟨isNaturalLThreeTwo_of_sup hN2 h3a, h3b, f, fun l hl => hf l (Subgroup.mem_sup_left hl)⟩

end Row26X

section Row26X2

variable {X : Type} [Group X] [Finite X]

theorem commute_action_of_mem_cMLStar {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hL : L.map (toStar T) = Ls) {x : X}
    (hx : toStar T x ∈ Subgroup.centralizer (Ls : Set (X ⧸ gnC T)))
    {U : Subgroup X} (hU : U ≤ gnV T) :
    ∀ l ∈ L, ∀ u ∈ U, x * (l * u * l⁻¹) * x⁻¹ = l * (x * u * x⁻¹) * l⁻¹ := by
  intro l hl u hu
  have hVn : (gnV T).Normal := Subgroup.normalClosure_normal
  have hlLs : toStar T l ∈ Ls := hL ▸ Subgroup.mem_map_of_mem _ hl
  have hcomm := (Subgroup.mem_centralizer_iff.1 hx) (toStar T l) hlLs
  have hc : l⁻¹ * (x * l * x⁻¹) ∈ gnC T := by
    rw [← QuotientGroup.eq_one_iff (N := gnC T)]
    have : (toStar T) (l⁻¹ * (x * l * x⁻¹)) = 1 := by
      simp only [map_mul, map_inv]
      have h' : toStar T l * toStar T x = toStar T x * toStar T l := hcomm
      calc (toStar T l)⁻¹ * (toStar T x * toStar T l * (toStar T x)⁻¹)
          = (toStar T l)⁻¹ * (toStar T l * toStar T x * (toStar T x)⁻¹) := by rw [h']
        _ = 1 := by group
    exact this
  have hxu : x * u * x⁻¹ ∈ gnV T := hVn.conj_mem u (hU hu) x
  have hcv := Subgroup.mem_centralizer_iff.1 hc
  have hz : (l⁻¹ * (x * l * x⁻¹)) * (x * u * x⁻¹) = (x * u * x⁻¹) * (l⁻¹ * (x * l * x⁻¹)) :=
    (hcv _ hxu).symm
  calc x * (l * u * l⁻¹) * x⁻¹
      = (x * l * x⁻¹) * (x * u * x⁻¹) * (x * l * x⁻¹)⁻¹ := by group
    _ = l * ((l⁻¹ * (x * l * x⁻¹)) * (x * u * x⁻¹) * (l⁻¹ * (x * l * x⁻¹))⁻¹) * l⁻¹ := by group
    _ = l * (x * u * x⁻¹) * l⁻¹ := by rw [hz]; group

theorem mem_normalizer_commutator {L V : Subgroup X} [hV : V.Normal] {x : X}
    (hx : L.map (MulAut.conj x).toMonoidHom = L) :
    x ∈ Subgroup.normalizer ((⁅L, V⁆ : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff_map_conj_eq]
  have hVx : V.map (MulAut.conj x).toMonoidHom = V := by
    have : x ∈ Subgroup.normalizer (V : Set X) := by
      rw [Subgroup.normalizer_eq_top_iff.2 hV]; exact Subgroup.mem_top x
    exact mem_normalizer_iff_map_conj_eq.1 this
  show Subgroup.map (MulAut.conj x).toMonoidHom ⁅L, V⁆ = ⁅L, V⁆
  rw [Subgroup.map_commutator L V (MulAut.conj x).toMonoidHom, hx, hVx]

theorem le_normalizer_commutator_s15 {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} :
    L ≤ Subgroup.normalizer ((⁅L, gnV T⁆ : Subgroup X) : Set X) := by
  intro l hl
  haveI : (gnV T).Normal := Subgroup.normalClosure_normal
  exact mem_normalizer_commutator (liftOf_conj_aux1 (Subgroup.le_normalizer hl))

end Row26X2

section Row26M

variable {X : Type} [Group X] [Finite X]

theorem conj_mem_CY {T T₁ T₂ : Subgroup X} (h : IsGNPair T T₁ T₂) {I : Subgroup X}
    (hI : I ∈ CY T T₁ T₂) {t : X} (ht : t ∈ T) : conjSub t I ∈ CY T T₁ T₂ := by
  obtain ⟨Is, hIs, hIl⟩ := hI
  refine ⟨Is.map (MulAut.conj (toStar T t)).toMonoidHom, gnYComponent_conj h hIs ht,
    liftOf_conj_aux4 hIl.1 t, ?_⟩
  have hcomp : (toStar T).comp (MulAut.conj t).toMonoidHom =
      (MulAut.conj (toStar T t)).toMonoidHom.comp (toStar T) := by
    ext a
    simp [MulAut.conj_apply]
  show (I.map (MulAut.conj t).toMonoidHom).map (toStar T) = _
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hIl.2]

end Row26M

section Row26G

variable {G : Type} [Group G] [Finite G]

theorem isTwoLocal_centralizer_of_sq {u : G} (hu1 : u ≠ 1) (hu2 : u * u = 1) :
    IsTwoLocal (Subgroup.centralizer ({u} : Set G)) := by
  have hord : orderOf u = 2 := by
    have h1 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hu2)
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hu1
    · exact h
  refine ⟨Subgroup.zpowers u, ?_, ?_, ?_⟩
  · rw [Ne, Subgroup.zpowers_eq_bot]; exact hu1
  · have hc : Nat.card (Subgroup.zpowers u) = 2 ^ 1 := by rw [Nat.card_zpowers, hord]; norm_num
    exact IsPGroup.of_card hc
  · apply le_antisymm
    · exact CFSG.RankThree.PartOne.StrongP.centralizer_singleton_le_normalizer_zpowers u
    · intro g hg
      have hmem : g * u * g⁻¹ ∈ Subgroup.zpowers u :=
        (Subgroup.mem_normalizer_iff.1 hg u).1 (Subgroup.mem_zpowers u)
      have hall : ∀ y ∈ Subgroup.zpowers u, y = 1 ∨ y = u := by
        intro y hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        have hu2' : u ^ 2 = 1 := by simpa [pow_two] using hu2
        have : u ^ k = u ^ (k % 2) := by
          conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul]
          simp [hu2']
        rw [this]
        rcases Int.emod_two_eq_zero_or_one k with h | h <;> simp [h]
      have hne : g * u * g⁻¹ ≠ 1 := by
        intro h
        apply hu1
        simpa using h
      rcases hall _ hmem with h | h
      · exact absurd h hne
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.1 hy]
        have : g * u = u * g := by
          calc g * u = (g * u * g⁻¹) * g := by group
            _ = u * g := by rw [h]
        exact this.symm

theorem centralizer_le_of_two_le_pRank_gen {M : Subgroup G} {P : Sylow 7 G}
    (hw : IsWitnessGen 7 P M) {u : G} (hu1 : u ≠ 1) (hu2 : u * u = 1)
    {R : Subgroup G} (hRM : R ≤ M) (hRc : R ≤ Subgroup.centralizer ({u} : Set G))
    (hR : 2 ≤ CFSG.Open.pRank 7 R) :
    Subgroup.centralizer ({u} : Set G) ≤ M :=
  hw.le_of_le_of_two_le_pRank Nat.prime_seven hRM hR
    (isTwoLocal_centralizer_of_sq hu1 hu2) hRc

theorem isTI_of_centralizer_le {M U : Subgroup G} (hUM : U ≤ M)
    (hTIM : ∀ m ∈ M, U.map (MulAut.conj m).toMonoidHom = U ∨
      U ⊓ U.map (MulAut.conj m).toMonoidHom = ⊥)
    (hC : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ M ∧
      7 ∣ Nat.card ↥(M ⊓ Subgroup.centralizer ({u} : Set G)))
    (hstrong : CFSG.RankThree.PartOne.IsStronglyPEmbedded 7 M) :
    CFSG.CGT.Timmesfeld75.IsTI U := by
  intro g
  by_cases hbot : U ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g U = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨⟨u, hu⟩, hu1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbot
    have hu1 : u ≠ 1 := fun h => hu1' (Subtype.ext h)
    obtain ⟨huU, hug⟩ := Subgroup.mem_inf.1 hu
    obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.1 hug
    have hvu' : g * v * g⁻¹ = u := by simpa [MulAut.conj_apply] using hvu
    have hv1 : v ≠ 1 := by
      rintro rfl
      apply hu1
      rw [← hvu']
      simp
    obtain ⟨hCv, -⟩ := hC v hv hv1
    obtain ⟨-, h7u⟩ := hC u huU hu1
    have hgM : g ∈ M := by
      by_contra hgM
      refine hstrong.2.2 g hgM ?_
      refine h7u.trans (Subgroup.card_dvd_of_le (le_inf inf_le_left ?_))
      intro x hx
      obtain ⟨hxM, hxC⟩ := Subgroup.mem_inf.1 hx
      have hcv : g⁻¹ * x * g ∈ Subgroup.centralizer ({v} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        rw [Set.mem_singleton_iff.1 hs]
        have h1 : u * x = x * u := (Subgroup.mem_centralizer_iff.1 hxC) u rfl
        rw [← hvu'] at h1
        calc v * (g⁻¹ * x * g) = g⁻¹ * ((g * v * g⁻¹) * x) * g := by group
          _ = g⁻¹ * (x * (g * v * g⁻¹)) * g := by rw [h1]
          _ = g⁻¹ * x * g * v := by group
      exact ⟨g⁻¹ * x * g, hCv hcv, by simp [MulAut.conj_apply, mul_assoc]⟩
    rcases hTIM g hgM with h | h
    · exact inf_eq_left.2 (le_of_eq h.symm)
    · exact absurd h hbot

theorem map_subtype_conjSub {M : Subgroup G} (U : Subgroup ↥M) (x : ↥M) :
    (conjSub x U).map M.subtype = (U.map M.subtype).map (MulAut.conj (x : G)).toMonoidHom := by
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem pRank_map_subtype {M : Subgroup G} (R : Subgroup ↥M) (p : ℕ) :
    CFSG.Open.pRank p (R.map M.subtype) = CFSG.Open.pRank p R :=
  CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective p M.subtype_injective R

end Row26G

section Row26Four

variable {G : Type} [Group G] [Finite G]

theorem isTI_conj_form {A : Subgroup G} (h : CFSG.CGT.Timmesfeld75.IsTI A) (g : G) :
    A.map (MulAut.conj g).toMonoidHom = A ∨ A ⊓ A.map (MulAut.conj g).toMonoidHom = ⊥ := by
  rcases h g with h1 | h2
  · right; exact h1
  · left
    have hle : A ≤ A.map (MulAut.conj g).toMonoidHom := by
      have h3 : A ⊓ A.map (MulAut.conj g).toMonoidHom = A := h2
      exact h3.symm.le.trans inf_le_right
    have hcard : Nat.card (A.map (MulAut.conj g).toMonoidHom) = Nat.card A :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    exact (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm

theorem tiPair_normalizes {T A B : Subgroup G} (hT : IsPGroup 2 T) (hAT : A ≤ T) (hBT : B ≤ T)
    (hA : IsElemAbelian 2 A) (hB : IsElemAbelian 2 B) (hTIA : CFSG.CGT.Timmesfeld75.IsTI A)
    (hTIB : CFSG.CGT.Timmesfeld75.IsTI B) (hN : A ⊓ Subgroup.normalizer (B : Set G) ≠ ⊥)
    (hcard : Nat.card B ≤ Nat.card A) : A ⊔ B ≤ Subgroup.normalizer (A : Set G) :=
  normalizer_of_TI_pair hT hAT hBT hA hB (fun h _ => isTI_conj_form hTIA h)
    (fun h _ => isTI_conj_form hTIB h) hN hcard

end Row26Four

section YSimple

variable {X : Type} [Group X] [Finite X]

theorem eq_ystar_of_simple {T T₁ T₂ : Subgroup X} (hS : IsSimpleGroup ↥(Ystar T T₁ T₂))
    {Ls : Subgroup (X ⧸ gnC T)} (hLs : GNYComponent T T₁ T₂ Ls) : Ls = Ystar T T₁ T₂ := by
  have hle : Ls ≤ Ystar T T₁ T₂ :=
    le_iSup₂ (f := fun L (_ : L ∈ {L : Subgroup (X ⧸ gnC T) | GNYComponent T T₁ T₂ L}) => L) Ls hLs
  have hnorm : Ystar T T₁ T₂ ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) := by
    refine iSup₂_le fun J hJ => ?_
    by_cases hJL : J = Ls
    · subst hJL
      exact Subgroup.le_normalizer
    · have hc := kComp_holds.1 (X ⧸ gnC T) J Ls hJ.1 hLs.1 hJL
      have hcen : J ≤ Subgroup.centralizer (Ls : Set (X ⧸ gnC T)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc
      exact hcen.trans (Subgroup.centralizer_le_normalizer _)
  haveI : (Ls.subgroupOf (Ystar T T₁ T₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 hnorm
  rcases hS.eq_bot_or_eq_top_of_normal (Ls.subgroupOf (Ystar T T₁ T₂)) with h | h
  · exfalso
    have hLsbot : Ls = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hle hx⟩ : ↥(Ystar T T₁ T₂)) ∈ Ls.subgroupOf (Ystar T T₁ T₂) := hx
      rw [h, Subgroup.mem_bot] at hx'
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val hx'
    have hs : IsSimpleGroup (↥Ls ⧸ Subgroup.center ↥Ls) := hLs.1.2.2.2
    obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
    apply hab
    have h3 : Subsingleton ↥Ls := by
      rw [hLsbot]; exact inferInstance
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    rw [Subsingleton.elim a' b']
  · apply le_antisymm hle
    intro y hy
    have : (⟨y, hy⟩ : ↥(Ystar T T₁ T₂)) ∈ Ls.subgroupOf (Ystar T T₁ T₂) := by
      rw [h]; exact Subgroup.mem_top _
    exact this

theorem eq_of_mem_CY_of_simple {T T₁ T₂ : Subgroup X}
    (hX : GNSetting X T) (hS : IsSimpleGroup ↥(Ystar T T₁ T₂)) {Ls : Subgroup (X ⧸ gnC T)}
    {L : Subgroup X} (hLs : GNYComponent T T₁ T₂ Ls) (hL : LiftOf T L Ls) {I : Subgroup X}
    (hI : I ∈ CY T T₁ T₂) : I = L := by
  obtain ⟨Is, hIs, hIl⟩ := hI
  have h1 : Is = Ystar T T₁ T₂ := eq_ystar_of_simple hS hIs
  have h2 : Ls = Ystar T T₁ T₂ := eq_ystar_of_simple hS hLs
  rw [h1, ← h2] at hIl
  exact liftOf_unique hX hLs.1 hIl hL

theorem yLifts_eq_of_simple {T T₁ T₂ : Subgroup X} (hX : GNSetting X T)
    (hS : IsSimpleGroup ↥(Ystar T T₁ T₂)) {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X}
    (hLs : GNYComponent T T₁ T₂ Ls) (hL : LiftOf T L Ls) : yLifts T T₁ T₂ = L :=
  le_antisymm (iSup₂_le fun I hI => (eq_of_mem_CY_of_simple hX hS hLs hL hI).le)
    (le_iSup₂ (f := fun L (_ : L ∈ CY T T₁ T₂) => L) L ⟨Ls, hLs, hL⟩)

end YSimple

section Row27

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_of_two_le_pRank_gen {M W : Subgroup G} {P : Sylow 7 G}
    (hw : IsWitnessGen 7 P M) (hW : W ≠ ⊥) (hW2 : IsPGroup 2 W) {R : Subgroup G}
    (hRM : R ≤ M) (hRW : R ≤ Subgroup.normalizer (W : Set G))
    (hR : 2 ≤ CFSG.Open.pRank 7 R) :
    Subgroup.normalizer (W : Set G) ≤ M :=
  hw.le_of_le_of_two_le_pRank Nat.prime_seven hRM hR ⟨W, hW, hW2, rfl⟩ hRW

end Row27

section Row27B

variable {G : Type} [Group G] [Finite G]

theorem ystar_eq_of_unique {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}
    (hLifts : ∀ Ls : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Ls → ∃ L, LiftOf T L Ls)
    (huniq : ∀ I ∈ CY T T₁ T₂, ∀ I' ∈ CY T T₁ T₂, I = I')
    {Ls : Subgroup (X ⧸ gnC T)} (hLs : GNYComponent T T₁ T₂ Ls) : Ystar T T₁ T₂ = Ls := by
  apply le_antisymm
  · refine iSup₂_le fun J hJ => ?_
    obtain ⟨I, hI⟩ := hLifts J hJ
    obtain ⟨L, hL⟩ := hLifts Ls hLs
    have h := huniq I ⟨J, hJ, hI⟩ L ⟨Ls, hLs, hL⟩
    rw [← hI.2, ← hL.2, h]
  · exact le_iSup₂ (f := fun L (_ : L ∈ {L : Subgroup (X ⧸ gnC T) | GNYComponent T T₁ T₂ L}) => L) Ls hLs

end Row27B

end CFSG.LocalAnalysis.RankThreeUC.S15
