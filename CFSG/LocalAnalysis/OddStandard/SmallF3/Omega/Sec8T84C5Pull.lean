module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Fink
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C3Def

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

open Subgroup

private lemma mem_pull {G Γ : Type} [Group G] [Group Γ] {N : Subgroup G}
    (κ : ↥N →* Γ) (M : Subgroup Γ) (x : G) :
    x ∈ (M.comap κ).map N.subtype ↔ ∃ h : x ∈ N, κ ⟨x, h⟩ ∈ M := by
  simp only [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hh⟩
    exact ⟨⟨x, h⟩, hh, rfl⟩

private lemma quotEquivTo_pull {G Γ F : Type} [Group G] [Group Γ] [Group F]
    {N P : Subgroup G} (hPN : P ≤ N) (κ : ↥N →* Γ) (M : Subgroup Γ)
    (hker : ∀ x : ↥N, κ x = 1 ↔ (x : G) ∈ P)
    (hM : M ≤ κ.range) (hQ : QuotEquivTo M ⊥ F) :
    QuotEquivTo ((M.comap κ).map N.subtype) P F := by
  obtain ⟨φ, hφsurj, hφker⟩ := hQ
  have hφker_bot : φ.ker = ⊥ := by
    simpa using hφker
  let X : Subgroup G := (M.comap κ).map N.subtype
  have hXN : X ≤ N := Subgroup.map_subtype_le _
  let e : ↥X →* ↥N := Subgroup.inclusion hXN
  let κX : ↥X →* Γ := κ.comp e
  have hκX : ∀ x : ↥X, κX x ∈ M := by
    intro x
    obtain ⟨hxN, hxM⟩ := (mem_pull κ M (x : G)).mp x.2
    have hx : κX x = κ ⟨(x : G), hxN⟩ := by
      apply congrArg κ
      apply Subtype.ext
      simp [e]
    rwa [hx]
  let toM : ↥X →* ↥M := κX.codRestrict M hκX
  let ψ : ↥X →* F := φ.comp toM
  refine ⟨ψ, ?_, ?_⟩
  · intro a
    obtain ⟨m, hm⟩ := hφsurj a
    have hmH : (m : Γ) ∈ κ.range := hM m.2
    obtain ⟨n, hn⟩ := MonoidHom.mem_range.mp hmH
    have hnX : (n : G) ∈ X := by
      rw [show X = (M.comap κ).map N.subtype from rfl]
      refine Subgroup.mem_map.mpr ⟨n, ?_, rfl⟩
      rw [Subgroup.mem_comap, hn]
      exact m.2
    refine ⟨⟨(n : G), hnX⟩, ?_⟩
    have htoM : toM ⟨(n : G), hnX⟩ = m := by
      apply Subtype.ext
      change κX ⟨(n : G), hnX⟩ = (m : Γ)
      have hxn : κX ⟨(n : G), hnX⟩ = κ n := by
        apply congrArg κ
        apply Subtype.ext
        simp [e]
      rw [hxn]
      exact hn
    change φ (toM ⟨(n : G), hnX⟩) = a
    rw [htoM]
    exact hm
  · ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    have hψ : ψ x = 1 ↔ toM x = 1 := by
      change φ (toM x) = 1 ↔ toM x = 1
      rw [← MonoidHom.mem_ker, hφker_bot]
      exact Subgroup.mem_bot
    rw [hψ]
    constructor
    · intro h
      have hc : κX x = 1 := by
        have := congrArg (fun y : ↥M => (y : Γ)) h
        simpa [toM] using this
      have hxP := (hker (Subgroup.inclusion hXN x)).mp (by simpa [κX, e] using hc)
      simpa using hxP
    · intro hx
      apply Subtype.ext
      change κX x = 1
      exact (hker (Subgroup.inclusion hXN x)).mpr (by simpa [e] using hx)

theorem sec8X_of_wreathMod {G : Type} [Group G] [Finite G] (t : G) (E : Subgroup G)
    {Γ : Type} [Group Γ] (κ : ↥(normalizer (E : Set G)) →* Γ)
    (hker : ∀ x : ↥(normalizer (E : Set G)), κ x = 1 ↔ (x : G) ∈ centralizer (E : Set G))
    (ht : t ∈ normalizer (E : Set G)) (H M1 M2 : Subgroup Γ) (hH : κ.range = H)
    (hW : WreathMod H ⊥ M1 M2 (κ ⟨t, ht⟩)) :
    ∃ X1 X2 : Subgroup G, Sec8X G t E X1 X2 := by
  let N : Subgroup G := normalizer (E : Set G)
  let C : Subgroup G := centralizer (E : Set G)
  let X1 : Subgroup G := (M1.comap κ).map N.subtype
  let X2 : Subgroup G := (M2.comap κ).map N.subtype
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer (E : Set G)
  have hX1N : X1 ≤ N := Subgroup.map_subtype_le _
  have hX2N : X2 ≤ N := Subgroup.map_subtype_le _
  have hmem1 : ∀ x : G, x ∈ X1 ↔ ∃ h : x ∈ N, κ ⟨x, h⟩ ∈ M1 := by
    intro x
    simpa [X1, N] using mem_pull κ M1 x
  have hmem2 : ∀ x : G, x ∈ X2 ↔ ∃ h : x ∈ N, κ ⟨x, h⟩ ∈ M2 := by
    intro x
    simpa [X2, N] using mem_pull κ M2 x
  have hc1 : C ≤ X1 := by
    intro c hc
    rw [hmem1 c]
    refine ⟨hCN hc, ?_⟩
    have h1 : κ ⟨c, hCN hc⟩ = 1 := (hker ⟨c, hCN hc⟩).mpr hc
    rw [h1]
    exact M1.one_mem
  have hc2 : C ≤ X2 := by
    intro c hc
    rw [hmem2 c]
    refine ⟨hCN hc, ?_⟩
    have h1 : κ ⟨c, hCN hc⟩ = 1 := (hker ⟨c, hCN hc⟩).mpr hc
    rw [h1]
    exact M2.one_mem
  refine ⟨X1, X2, ?_⟩
  refine
    { c_le1 := hc1
      c_le2 := hc2
      le1 := hX1N
      le2 := hX2N
      comm := ?_
      inf := ?_
      sup := ?_
      t_not := ?_
      swap1 := ?_
      swap2 := ?_
      quot1 := ?_
      quot2 := ?_ }
  · intro a ha b hb
    obtain ⟨haN, haM⟩ := (hmem1 a).mp ha
    obtain ⟨hbN, hbM⟩ := (hmem2 b).mp hb
    have habN : a * b * a⁻¹ * b⁻¹ ∈ N :=
      N.mul_mem (N.mul_mem (N.mul_mem haN hbN) (N.inv_mem haN)) (N.inv_mem hbN)
    have hk : κ ⟨a * b * a⁻¹ * b⁻¹, habN⟩ = 1 := by
      have he : (⟨a * b * a⁻¹ * b⁻¹, habN⟩ : ↥N) =
          ⟨a, haN⟩ * ⟨b, hbN⟩ * ⟨a, haN⟩⁻¹ * ⟨b, hbN⟩⁻¹ := by
        ext
        simp [mul_assoc]
      rw [he]
      simp only [map_mul, map_inv]
      have hcomm := hW.comm (κ ⟨a, haN⟩) haM (κ ⟨b, hbN⟩) hbM
      simpa using hcomm
    exact (hker ⟨a * b * a⁻¹ * b⁻¹, habN⟩).mp hk
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hx1N, hx1M⟩ := (hmem1 x).mp hx1
    obtain ⟨hx2N, hx2M⟩ := (hmem2 x).mp hx2
    have hboth : κ ⟨x, hx1N⟩ ∈ M1 ⊓ M2 := by
      refine Subgroup.mem_inf.mpr ⟨hx1M, ?_⟩
      simpa using hx2M
    have hbot : κ ⟨x, hx1N⟩ ∈ (⊥ : Subgroup Γ) := hW.inf hboth
    have hk : κ ⟨x, hx1N⟩ = 1 := by simpa using hbot
    exact (hker ⟨x, hx1N⟩).mp hk
  · apply le_antisymm
    · refine sup_le (sup_le hX1N hX2N) ?_
      rw [Subgroup.zpowers_le]
      exact ht
    · intro n hn
      let n' : ↥N := ⟨n, hn⟩
      let D : Subgroup G := X1 ⊔ X2 ⊔ zpowers t
      let Y : Subgroup ↥N := D.comap N.subtype
      change n ∈ D
      have hker_le_Y : κ.ker ≤ Y := by
        intro x hx
        rw [MonoidHom.mem_ker] at hx
        have hxC : (x : G) ∈ C := (hker x).mp hx
        have hxX1 : (x : G) ∈ X1 := hc1 hxC
        change (x : G) ∈ D
        exact (show X1 ≤ D from le_sup_left.trans le_sup_left) hxX1
      have hHle : H ≤ Y.map κ := by
        rw [← hW.sup]
        refine sup_le (sup_le ?_ ?_) ?_
        · intro m hm
          have hmH : m ∈ κ.range := by
            rw [hH]
            exact hW.le1 hm
          obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hmH
          have hxX1 : (x : G) ∈ X1 := by
            rw [hmem1]
            exact ⟨x.2, by simpa [hx] using hm⟩
          have hxY : x ∈ Y := by
            change (x : G) ∈ D
            exact (show X1 ≤ D from le_sup_left.trans le_sup_left) hxX1
          exact Subgroup.mem_map.mpr ⟨x, hxY, hx⟩
        · intro m hm
          have hmH : m ∈ κ.range := by
            rw [hH]
            exact hW.le2 hm
          obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hmH
          have hxX2 : (x : G) ∈ X2 := by
            rw [hmem2]
            exact ⟨x.2, by simpa [hx] using hm⟩
          have hxY : x ∈ Y := by
            change (x : G) ∈ D
            exact (show X2 ≤ D from le_sup_right.trans le_sup_left) hxX2
          exact Subgroup.mem_map.mpr ⟨x, hxY, hx⟩
        · rw [Subgroup.zpowers_le]
          have htD : t ∈ D :=
            (show zpowers t ≤ D from le_sup_right) (Subgroup.mem_zpowers t)
          have htY : (⟨t, ht⟩ : ↥N) ∈ Y := by
            change t ∈ D
            exact htD
          simpa using Subgroup.mem_map_of_mem κ htY
      have hkn : κ n' ∈ H := by
        rw [← hH]
        exact MonoidHom.mem_range.mpr ⟨n', rfl⟩
      obtain ⟨y, hyY, hky⟩ := Subgroup.mem_map.mp (hHle hkn)
      have hny : n' * y⁻¹ ∈ κ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hky, mul_inv_cancel]
      have hnyY : n' * y⁻¹ ∈ Y := hker_le_Y hny
      have hn'Y : n' ∈ Y := by
        simpa using Y.mul_mem hnyY hyY
      simpa [n'] using (Subgroup.mem_comap.mp hn'Y)
  · intro ht12
    have htK : (⟨t, ht⟩ : ↥N) ∈ (X1 ⊔ X2).comap N.subtype := by
      rw [Subgroup.mem_comap]
      exact ht12
    have hX1comap : X1.comap N.subtype ≤ M1.comap κ := by
      intro y hy
      rw [Subgroup.mem_comap] at hy ⊢
      obtain ⟨h, hh⟩ := (hmem1 (y : G)).mp hy
      simpa using hh
    have hX2comap : X2.comap N.subtype ≤ M2.comap κ := by
      intro y hy
      rw [Subgroup.mem_comap] at hy ⊢
      obtain ⟨h, hh⟩ := (hmem2 (y : G)).mp hy
      simpa using hh
    have hKle : (X1 ⊔ X2).comap N.subtype ≤ (M1 ⊔ M2).comap κ := by
      rw [← Subgroup.comap_sup_eq_of_le_range (f := N.subtype)
        (by simpa using hX1N) (by simpa using hX2N)]
      exact sup_le (hX1comap.trans (Subgroup.comap_mono le_sup_left))
        (hX2comap.trans (Subgroup.comap_mono le_sup_right))
    exact hW.u_not (hKle htK)
  · intro a ha
    obtain ⟨haN, haM⟩ := (hmem1 a).mp ha
    rw [hmem2 (t * a * t⁻¹)]
    have htaN : t * a * t⁻¹ ∈ N :=
      N.mul_mem (N.mul_mem ht haN) (N.inv_mem ht)
    refine ⟨htaN, ?_⟩
    have he : (⟨t * a * t⁻¹, htaN⟩ : ↥N) =
        ⟨t, ht⟩ * ⟨a, haN⟩ * ⟨t, ht⟩⁻¹ := by
      ext
      simp [mul_assoc]
    have hk : κ ⟨t * a * t⁻¹, htaN⟩ =
        κ ⟨t, ht⟩ * κ ⟨a, haN⟩ * (κ ⟨t, ht⟩)⁻¹ := by
      rw [he]
      simp only [map_mul, map_inv]
    rw [hk]
    exact hW.swap1 (κ ⟨a, haN⟩) haM
  · intro a ha
    obtain ⟨haN, haM⟩ := (hmem2 a).mp ha
    rw [hmem1 (t * a * t⁻¹)]
    have htaN : t * a * t⁻¹ ∈ N :=
      N.mul_mem (N.mul_mem ht haN) (N.inv_mem ht)
    refine ⟨htaN, ?_⟩
    have he : (⟨t * a * t⁻¹, htaN⟩ : ↥N) =
        ⟨t, ht⟩ * ⟨a, haN⟩ * ⟨t, ht⟩⁻¹ := by
      ext
      simp [mul_assoc]
    have hk : κ ⟨t * a * t⁻¹, htaN⟩ =
        κ ⟨t, ht⟩ * κ ⟨a, haN⟩ * (κ ⟨t, ht⟩)⁻¹ := by
      rw [he]
      simp only [map_mul, map_inv]
    rw [hk]
    exact hW.swap2 (κ ⟨a, haN⟩) haM
  · have hM1le : M1 ≤ κ.range := by
      rw [hH]
      exact hW.le1
    simpa [X1, C, N] using quotEquivTo_pull hCN κ M1 hker hM1le hW.quot1
  · have hM2le : M2 ≤ κ.range := by
      rw [hH]
      exact hW.le2
    simpa [X2, C, N] using quotEquivTo_pull hCN κ M2 hker hM2le hW.quot2

end C10

end CFSG.OddStandard.SmallF3.Omega
