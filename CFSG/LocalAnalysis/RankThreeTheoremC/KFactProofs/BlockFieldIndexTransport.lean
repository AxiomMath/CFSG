module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexLeviGeneric
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexAbstract

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabPrime
open scoped commutatorElement

theorem eqOn_of_perfect_central {A B : Type*} [Group A] [Group B] (f₁ f₂ : A →* B)
    {V : Subgroup A} (hV : ⁅V, V⁆ = V)
    (h : ∀ x ∈ V, f₁ x * (f₂ x)⁻¹ ∈ Subgroup.center B) : ∀ x ∈ V, f₁ x = f₂ x := by
  have hle : ⁅V, V⁆ ≤ MonoidHom.eqLocus f₁ f₂ := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hσ : ∀ z ∈ V, f₁ z = f₂ z * (f₁ z * (f₂ z)⁻¹) := fun z hz => by
      have := Subgroup.mem_center_iff.1 (h z hz) (f₂ z)
      rw [this]; group
    show f₁ ⁅x, y⁆ = f₂ ⁅x, y⁆
    rw [map_commutatorElement, map_commutatorElement, hσ x hx, hσ y hy]
    exact commutatorElement_mul_central (h x hx) (h y hy)
  intro x hx
  have hx' : x ∈ ⁅V, V⁆ := by rw [hV]; exact hx
  exact hle hx'

theorem map_perfectJoin_range {A B : Type*} [Group A] [Group B] (θ : A →* B)
    (hker : θ.ker ≤ Subgroup.center A) :
    (perfectJoin (⊤ : Subgroup A)).map θ = perfectJoin θ.range := by
  refine le_antisymm (le_perfectJoin (Subgroup.map_le_range θ _) ?_) ?_
  · rw [← Subgroup.map_commutator, perfectJoin_perfect]
  · obtain ⟨W, hW, -, hWmap⟩ := exists_perfect_map_eq θ hker (perfectJoin_perfect θ.range)
      (perfectJoin_le _)
    rw [← hWmap]
    exact Subgroup.map_mono (le_perfectJoin le_top hW)

theorem map_subtype_perfectJoin {Y : Type*} [Group Y] {L P : Subgroup Y} (hPL : P ≤ L) :
    (perfectJoin (P.subgroupOf L)).map L.subtype = perfectJoin P := by
  refine le_antisymm (le_perfectJoin ?_ ?_) ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact perfectJoin_le (P.subgroupOf L) hx
  · rw [← Subgroup.map_commutator, perfectJoin_perfect]
  · have hVL : perfectJoin P ≤ L := (perfectJoin_le P).trans hPL
    have h1 : (perfectJoin P).subgroupOf L ≤ perfectJoin (P.subgroupOf L) := by
      refine le_perfectJoin (fun x hx => perfectJoin_le P hx) ?_
      apply Subgroup.map_injective L.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hVL]
      exact perfectJoin_perfect P
    calc perfectJoin P = ((perfectJoin P).subgroupOf L).map L.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hVL).symm
      _ ≤ _ := Subgroup.map_mono h1

theorem map_le_pCoreOf {A Y : Type*} [Group A] [Group Y] (θ : A →* Y) {VA M : Subgroup A}
    (hMV : M ≤ VA) (hnorm : ∀ x ∈ VA, ∀ m ∈ M, x * m * x⁻¹ ∈ M) (h2 : IsPGroup 2 M) :
    M.map θ ≤ pCoreOf 2 (VA.map θ) := by
  set V : Subgroup Y := VA.map θ with hV
  set N : Subgroup Y := M.map θ with hN
  have hNV : N ≤ V := Subgroup.map_mono hMV
  have hNn : (N.subgroupOf V).Normal := by
    refine ⟨fun n hn y => ?_⟩
    obtain ⟨m, hm, hmn⟩ : ∃ m ∈ M, θ m = (n : Y) :=
      Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hn)
    obtain ⟨x, hx, hxy⟩ : ∃ x ∈ VA, θ x = (y : Y) := Subgroup.mem_map.1 y.2
    rw [Subgroup.mem_subgroupOf]
    refine ⟨x * m * x⁻¹, hnorm x hx m hm, ?_⟩
    simp only [map_mul, map_inv, hmn, hxy]
    rfl
  have hN2 : IsPGroup 2 (N.subgroupOf V) := (h2.map θ).comap_subtype
  have h1 : N.subgroupOf V ≤ CFSG.pCore 2 ↥V :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hNn hN2
  calc N = (N.subgroupOf V).map V.subtype := (Subgroup.map_subgroupOf_eq_of_le hNV).symm
    _ ≤ (CFSG.pCore 2 ↥V).map V.subtype := Subgroup.map_mono h1

section Cover

variable {Y : Type*} [Group Y] {L : Subgroup Y} {K : Type*} [Group K]

abbrev coverSub (ρ : K →* ↥L) (P : Subgroup Y) : Subgroup K :=
  (P.subgroupOf L).comap ρ

@[expose] def coverHom (ρ : K →* ↥L) (P : Subgroup Y) : ↥(coverSub ρ P) →* ↥L :=
  ρ.comp (coverSub ρ P).subtype

@[expose] def coverHomY (ρ : K →* ↥L) (P : Subgroup Y) : ↥(coverSub ρ P) →* Y :=
  L.subtype.comp (coverHom ρ P)

theorem coverHom_range (ρ : K →* ↥L) (hρ : Function.Surjective ρ) (P : Subgroup Y) :
    (coverHom ρ P).range = P.subgroupOf L := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2
  · intro hy
    obtain ⟨x, rfl⟩ := hρ y
    exact ⟨⟨x, hy⟩, rfl⟩

theorem coverHom_ker_le_center (ρ : K →* ↥L) (hker : ρ.ker ≤ Subgroup.center K)
    (P : Subgroup Y) : (coverHom ρ P).ker ≤ Subgroup.center ↥(coverSub ρ P) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro z
  have hx1 : ρ (x : K) = 1 := hx
  have hxc : (x : K) ∈ Subgroup.center K := hker hx1
  exact Subtype.ext (Subgroup.mem_center_iff.1 hxc (z : K))

theorem map_perfectJoin_coverHomY (ρ : K →* ↥L) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center K) {P : Subgroup Y} (hPL : P ≤ L) :
    (perfectJoin (⊤ : Subgroup ↥(coverSub ρ P))).map (coverHomY ρ P) = perfectJoin P := by
  have h1 : (perfectJoin (⊤ : Subgroup ↥(coverSub ρ P))).map (coverHom ρ P) =
      perfectJoin (P.subgroupOf L) := by
    rw [map_perfectJoin_range _ (coverHom_ker_le_center ρ hker P), coverHom_range ρ hρ P]
  rw [coverHomY, ← Subgroup.map_map, h1]
  exact map_subtype_perfectJoin hPL

end Cover

theorem actsInnerly_of_levi_data
    {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y} [L.Normal] (hPL : P ≤ L)
    {K : Type} [Group K] [Finite K] (ρ : K →* ↥L) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center K) (Q : Subgroup K) (hQ : Q = coverSub ρ P)
    {k : ℕ} {G : Fin k → Type} [∀ j, Group (G j)] [∀ j, Finite (G j)]
    (S H : ∀ j, Subgroup (G j)) (β : ↥Q →* ∀ j, G j)
    (h2 : IsPGroup 2 β.ker) (hS : Subgroup.pi Set.univ S ≤ β.range)
    (hc : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S)
    (hqs : ∀ j, CFSG.Open.IsQuasisimple ↥(S j) ∨ Group.IsSolvable ↥(S j))
    (hblock : ∀ j, CFSG.Open.IsQuasisimple ↥(S j) → BlockOK (H j) (S j))
    (hZ : ∀ (j : Fin k) (E : Subgroup (G j)), E ≤ S j → IsElemAbelian 3 E → Nat.card E = 9 →
      ∀ x : ↥Q, ρ (x : K) = 1 → β x ∈ E.map (MonoidHom.mulSingle G j) → x = 1)
    (φ : MulAut ↥Q) (g : ∀ j, G j) (hg : ∀ j, g j ∈ H j)
    (hφ : ∀ x, β (φ x) = g * β x * g⁻¹) {a : Y}
    (hcompat : ∀ x : ↥Q,
      (MulAut.conjNormal a : MulAut ↥L) (ρ (x : K)) * (ρ ((φ x : ↥Q) : K))⁻¹ ∈
        Subgroup.center ↥L)
    (hpow : ∃ m : ℕ, ∀ w ∈ perfectJoin P, a ^ (3 ^ m) * w = w * a ^ (3 ^ m))
    (hrk : Open.pRank 3 (perfectJoin P) ≤ 1) :
    ∃ v ∈ perfectJoin P, ∀ w ∈ perfectJoin P, ⁅a * v, w⁆ ∈ pCoreOf 2 (perfectJoin P) := by
  subst hQ
  classical
  obtain ⟨m, hm⟩ := hpow
  have hker₀ := coverHom_ker_le_center ρ hker P
  have hVQperf : ⁅perfectJoin (⊤ : Subgroup ↥(coverSub ρ P)),
      perfectJoin (⊤ : Subgroup ↥(coverSub ρ P))⁆ = perfectJoin (⊤ : Subgroup ↥(coverSub ρ P)) :=
    perfectJoin_perfect _
  have hVQ := map_perfectJoin_coverHomY ρ hρ hker hPL
  have hVQstable : ∀ u ∈ perfectJoin (⊤ : Subgroup ↥(coverSub ρ P)),
      φ u ∈ perfectJoin (⊤ : Subgroup ↥(coverSub ρ P)) := fun u hu =>
    map_perfectJoin_le φ ⟨u, hu, rfl⟩
  have hVQstableN : ∀ n : ℕ, ∀ u ∈ perfectJoin (⊤ : Subgroup ↥(coverSub ρ P)),
      (φ ^ n) u ∈ perfectJoin (⊤ : Subgroup ↥(coverSub ρ P)) := by
    intro n
    induction n with
    | zero => intro u hu; simpa using hu
    | succ n ih =>
      intro u hu
      rw [pow_succ', MulAut.mul_apply]
      exact hVQstable _ (ih u hu)
  have h5 : ∀ u ∈ perfectJoin (⊤ : Subgroup ↥(coverSub ρ P)),
      (MulAut.conjNormal a : MulAut ↥L) (coverHom ρ P u) = coverHom ρ P (φ u) :=
    eqOn_of_perfect_central ((MulAut.conjNormal a : MulAut ↥L).toMonoidHom.comp (coverHom ρ P))
      ((coverHom ρ P).comp φ.toMonoidHom) hVQperf (fun x _ => hcompat x)
  have h6 : ∀ n : ℕ, ∀ u ∈ perfectJoin (⊤ : Subgroup ↥(coverSub ρ P)),
      ((MulAut.conjNormal a : MulAut ↥L) ^ n) (coverHom ρ P u) =
        coverHom ρ P ((φ ^ n) u) := by
    intro n
    induction n with
    | zero => intro u hu; simp
    | succ n ih =>
      intro u hu
      rw [pow_succ', pow_succ', MulAut.mul_apply, MulAut.mul_apply, ih u hu]
      exact h5 _ (hVQstableN n u hu)
  have h7 : ∀ x ∈ perfectJoin (⊤ : Subgroup ↥(coverSub ρ P)), (φ ^ (3 ^ m)) x = x := by
    have hcomm : ∀ x ∈ perfectJoin (⊤ : Subgroup ↥(coverSub ρ P)),
        (φ ^ (3 ^ m)).toMonoidHom x * (MonoidHom.id ↥(coverSub ρ P) x)⁻¹ ∈
          Subgroup.center ↥(coverSub ρ P) := by
      intro x hx
      apply hker₀
      rw [MonoidHom.mem_ker]
      change coverHom ρ P ((φ ^ (3 ^ m)) x * x⁻¹) = 1
      rw [map_mul, map_inv, ← h6 (3 ^ m) x hx, ← map_pow]
      have hxw : coverHomY ρ P x ∈ perfectJoin P := hVQ ▸ ⟨x, hx, rfl⟩
      have h8 : (MulAut.conjNormal (a ^ 3 ^ m) : MulAut ↥L) (coverHom ρ P x) =
          coverHom ρ P x := by
        apply Subtype.ext
        rw [MulAut.conjNormal_apply]
        change a ^ 3 ^ m * coverHomY ρ P x * (a ^ 3 ^ m)⁻¹ = coverHomY ρ P x
        rw [hm _ hxw]; group
      rw [h8, mul_inv_cancel]
    exact eqOn_of_perfect_central ((φ ^ (3 ^ m)).toMonoidHom) (MonoidHom.id _) hVQperf hcomm
  rcases inner_or_elemAbelian S H β hS hc hqs hblock φ g hg hφ m h7 with
    ⟨v, hv, hvw⟩ | ⟨j, E, hES, hE, hcard, hEV⟩
  · have hvY : coverHomY ρ P v⁻¹ ∈ perfectJoin P :=
      hVQ ▸ ⟨v⁻¹, Subgroup.inv_mem _ hv, rfl⟩
    refine ⟨coverHomY ρ P v⁻¹, hvY, fun w' hw' => ?_⟩
    rw [← hVQ] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    have huV : v⁻¹ * w * v ∈ perfectJoin (⊤ : Subgroup ↥(coverSub ρ P)) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hv) hw) hv
    have h5u : a * coverHomY ρ P (v⁻¹ * w * v) * a⁻¹ =
        coverHomY ρ P (φ (v⁻¹ * w * v)) := by
      have := congrArg (fun z : ↥L => (z : Y)) (h5 _ huV)
      simp only [MulAut.conjNormal_apply] at this
      exact this
    have hmemM : φ (v⁻¹ * w * v) * w⁻¹ ∈ perfectJoin (⊤ : Subgroup ↥(coverSub ρ P)) ⊓ β.ker := by
      refine ⟨Subgroup.mul_mem _ (hVQstable _ huV) (Subgroup.inv_mem _ hw), ?_⟩
      have h9 := hvw _ huV
      have e : v * (v⁻¹ * w * v) * v⁻¹ = w := by group
      rwa [e] at h9
    have hpc : (perfectJoin (⊤ : Subgroup ↥(coverSub ρ P)) ⊓ β.ker).map (coverHomY ρ P) ≤
        pCoreOf 2 (perfectJoin P) := by
      rw [← hVQ]
      refine map_le_pCoreOf (coverHomY ρ P) inf_le_left (fun x hx n hn => ⟨?_, ?_⟩)
        (h2.to_le inf_le_right)
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hn.1) (Subgroup.inv_mem _ hx)
      · show x * n * x⁻¹ ∈ β.ker
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, MonoidHom.mem_ker.1 hn.2,
          mul_one, mul_inv_cancel]
    have hcalc : ⁅a * coverHomY ρ P v⁻¹, coverHomY ρ P w⁆ =
        coverHomY ρ P (φ (v⁻¹ * w * v) * w⁻¹) := by
      calc ⁅a * coverHomY ρ P v⁻¹, coverHomY ρ P w⁆ =
          (a * coverHomY ρ P (v⁻¹ * w * v) * a⁻¹) * (coverHomY ρ P w)⁻¹ := by
            rw [map_mul (coverHomY ρ P), map_mul (coverHomY ρ P), map_inv (coverHomY ρ P),
              commutatorElement_def]; group
        _ = coverHomY ρ P (φ (v⁻¹ * w * v)) * (coverHomY ρ P w)⁻¹ := by rw [h5u]
        _ = coverHomY ρ P (φ (v⁻¹ * w * v) * w⁻¹) := by
            rw [map_mul (coverHomY ρ P), map_inv (coverHomY ρ P)]
    rw [hcalc]
    exact hpc ⟨_, hmemM, rfl⟩
  · exfalso
    have hÊel : IsElemAbelian 3 (E.map (MonoidHom.mulSingle G j)) :=
      CFSG.SectionRank.isElemAbelian_map hE _
    have hÊcard : Nat.card (E.map (MonoidHom.mulSingle G j)) = 9 := by
      rw [Subgroup.card_map_of_injective (f := MonoidHom.mulSingle G j) (Pi.mulSingle_injective j),
        hcard]
    obtain ⟨E', hE'V, hE'el, hE'card, hE'β, hE'inj⟩ := exists_lift_elemAbelian β h2 hEV hÊel
    have hθinj : ∀ x ∈ E', coverHomY ρ P x = 1 → x = 1 := by
      intro x hx h1
      have h2' : ρ (x : K) = 1 := Subtype.ext h1
      exact hZ j E hES hE hcard x h2' (hE'β x hx)
    have hE''V : E'.map (coverHomY ρ P) ≤ perfectJoin P := hVQ ▸ Subgroup.map_mono hE'V
    have hE''el : IsElemAbelian 3 (E'.map (coverHomY ρ P)) :=
      CFSG.SectionRank.isElemAbelian_map hE'el _
    have hE''card : Nat.card (E'.map (coverHomY ρ P)) = 3 ^ 2 := by
      have hbij : Function.Bijective (fun x : E' =>
          (⟨coverHomY ρ P x, ⟨x, x.2, rfl⟩⟩ : E'.map (coverHomY ρ P))) := by
        refine ⟨fun x y hxy => ?_, fun y => ?_⟩
        · have h1 : coverHomY ρ P ((x : ↥(coverSub ρ P))⁻¹ * y) = 1 := by
            rw [map_mul, map_inv]
            have := congrArg Subtype.val hxy
            simp only at this
            rw [this, inv_mul_cancel]
          have := hθinj _ (E'.mul_mem (E'.inv_mem x.2) y.2) h1
          exact Subtype.ext (inv_mul_eq_one.1 this)
        · obtain ⟨z, hz, hzy⟩ := y.2
          exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
      rw [← Nat.card_congr (Equiv.ofBijective _ hbij), hE'card, hÊcard]
      norm_num
    have := CFSG.SectionRank.le_pRank (by norm_num) hE''V hE''el hE''card
    omega

theorem leviInnAt_of_levi_data
    {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y} [L.Normal] (hPL : P ≤ L)
    {K : Type} [Group K] [Finite K] (ρ : K →* ↥L) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center K) (Q : Subgroup K) (hQ : Q = coverSub ρ P)
    {k : ℕ} {G : Fin k → Type} [∀ j, Group (G j)] [∀ j, Finite (G j)]
    (S H : ∀ j, Subgroup (G j)) (β : ↥Q →* ∀ j, G j)
    (h2 : IsPGroup 2 β.ker) (hS : Subgroup.pi Set.univ S ≤ β.range)
    (hc : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S)
    (hqs : ∀ j, CFSG.Open.IsQuasisimple ↥(S j) ∨ Group.IsSolvable ↥(S j))
    (hH : ∀ (x : ↥Q) (j : Fin k), β x j ∈ H j)
    (hblock : ∀ j, CFSG.Open.IsQuasisimple ↥(S j) → BlockOK (H j) (S j))
    (hZ : ∀ (j : Fin k) (E : Subgroup (G j)), E ≤ S j → IsElemAbelian 3 E → Nat.card E = 9 →
      ∀ x : ↥Q, ρ (x : K) = 1 → β x ∈ E.map (MonoidHom.mulSingle G j) → x = 1)
    (hrk : Open.pRank 3 (perfectJoin P) ≤ 1) : LeviInnAt P := by
  intro l hl m hcomm
  have hlL : l ∈ L := hPL hl
  obtain ⟨x, hx⟩ := hρ ⟨l, hlL⟩
  have hxQ : x ∈ Q := by
    rw [hQ]
    show ρ x ∈ P.subgroupOf L
    rw [hx]
    exact hl
  set x₀ : ↥Q := ⟨x, hxQ⟩ with hx₀
  refine actsInnerly_of_levi_data hPL ρ hρ hker Q hQ S H β h2 hS hc hqs hblock hZ
    (MulAut.conj x₀) (β x₀) (fun j => hH x₀ j) (fun y => ?_) (a := l) (fun y => ?_)
    ⟨m, fun w hw => ?_⟩ hrk
  · rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
  · have h1 : (MulAut.conjNormal l : MulAut ↥L) (ρ (y : K)) = ρ x * ρ (y : K) * (ρ x)⁻¹ := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      have := congrArg Subtype.val hx
      simp only at this
      rw [← this]
      rfl
    have h2' : ρ (((MulAut.conj x₀ y : ↥Q) : K)) = ρ x * ρ (y : K) * (ρ x)⁻¹ := by
      rw [MulAut.conj_apply]
      simp [hx₀, map_mul, map_inv]
    rw [h1, h2', mul_inv_cancel]
    exact Subgroup.one_mem _
  · exact (commutatorElement_eq_one_iff_mul_comm.1 (hcomm w hw))

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
