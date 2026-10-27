module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C3Def
public import CFSG.Open.FusionDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

open Subgroup CFSG.Open

private theorem quotEquivTo_map_comap {Γ : Type} [Group Γ] (H : Subgroup Γ)
    (O : Subgroup ↥H) [O.Normal] (N : Subgroup (↥H ⧸ O))
    (e : ↥N ≃* alternatingGroup (Fin 6)) :
    QuotEquivTo ((N.comap (QuotientGroup.mk' O)).map H.subtype) (O.map H.subtype)
      (alternatingGroup (Fin 6)) := by
  classical
  let π : ↥H →* (↥H ⧸ O) := QuotientGroup.mk' O
  let c : Subgroup ↥H := N.comap π
  let M : Subgroup Γ := c.map H.subtype
  let P : Subgroup Γ := O.map H.subtype
  let e1 : ↥c ≃* ↥M := Subgroup.equivMapOfInjective c H.subtype H.subtype_injective
  let ψ0 : ↥c →* ↥N := π.subgroupComap N
  let ψ : ↥M →* alternatingGroup (Fin 6) := e.toMonoidHom.comp (ψ0.comp e1.symm.toMonoidHom)
  have hker0 : ψ0.ker = O.subgroupOf c := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hx' : (ψ0 x : ↥H ⧸ O) = 1 := by rw [hx]; rfl
      exact (QuotientGroup.eq_one_iff (N := O) (x : ↥H)).mp hx'
    · intro hx
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (N := O) (x : ↥H)).mpr hx
  refine ⟨ψ, ?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := e.surjective y
    obtain ⟨z, hz⟩ := π.subgroupComap_surjective N (QuotientGroup.mk'_surjective (N := O)) x
    refine ⟨e1 z, ?_⟩
    change e (ψ0 (e1.symm (e1 z))) = y
    rw [MulEquiv.symm_apply_apply, hz, hx]
  · ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have hcoe : ((e1.symm x : ↥c) : Γ) = (x : Γ) := by
      have h1 := Subgroup.coe_equivMapOfInjective_apply c H.subtype H.subtype_injective
        (e1.symm x)
      rw [MulEquiv.apply_symm_apply] at h1
      exact h1.symm
    constructor
    · intro hx
      have h1 : ψ0 (e1.symm x) = 1 :=
        e.injective (by rw [show e (ψ0 (e1.symm x)) = 1 from hx, map_one])
      have h3 : (e1.symm x : ↥H) ∈ O := by
        have : e1.symm x ∈ ψ0.ker := MonoidHom.mem_ker.mpr h1
        rw [hker0] at this
        exact Subgroup.mem_subgroupOf.mp this
      exact Subgroup.mem_map.mpr ⟨(e1.symm x : ↥H), h3, hcoe⟩
    · intro hx
      obtain ⟨o, ho, hoeq⟩ := Subgroup.mem_map.mp hx
      have h2 : (e1.symm x : ↥H) ∈ O := by
        have heq : o = (e1.symm x : ↥H) := Subtype.ext (hoeq.trans hcoe.symm)
        rwa [heq] at ho
      have h3 : e1.symm x ∈ ψ0.ker := by
        rw [hker0]
        exact Subgroup.mem_subgroupOf.mpr h2
      have h4 : ψ0 (e1.symm x) = 1 := MonoidHom.mem_ker.mp h3
      change e (ψ0 (e1.symm x)) = 1
      rw [h4, map_one]

theorem wreathMod_of_dichotomy {Γ : Type} [Group Γ] [Finite Γ] (H : Subgroup Γ) (u : Γ)
    (hu : u ∈ H) (hu2 : u * u = 1)
    (N₁ N₂ : Subgroup (↥H ⧸ fusionOddCore ↥H))
    (hN₁ : Nonempty (↥N₁ ≃* alternatingGroup (Fin 6)))
    (hN₂ : Nonempty (↥N₂ ≃* alternatingGroup (Fin 6)))
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hdisj : Disjoint N₁ N₂)
    (hnorm : (N₁ ⊔ N₂).Normal) (hidx : (N₁ ⊔ N₂).index = 2)
    (hnot : (QuotientGroup.mk (⟨u, hu⟩ : ↥H) : ↥H ⧸ fusionOddCore ↥H) ∉ N₁ ⊔ N₂)
    (hconj : N₁.map (MulAut.conj
      (QuotientGroup.mk (⟨u, hu⟩ : ↥H) : ↥H ⧸ fusionOddCore ↥H)).toMonoidHom = N₂) :
    ∃ M1 M2 : Subgroup Γ, WreathMod H ((fusionOddCore ↥H).map H.subtype) M1 M2 u := by
  classical
  let O : Subgroup ↥H := fusionOddCore ↥H
  haveI hOnorm : O.Normal := fusionOddCore_normal ↥H
  let π : ↥H →* (↥H ⧸ O) := QuotientGroup.mk' O
  let q : ↥H ⧸ O := QuotientGroup.mk (⟨u, hu⟩ : ↥H)
  let c1 : Subgroup ↥H := N₁.comap π
  let c2 : Subgroup ↥H := N₂.comap π
  let M1 : Subgroup Γ := c1.map H.subtype
  let M2 : Subgroup Γ := c2.map H.subtype
  let P : Subgroup Γ := O.map H.subtype
  have hker : ∀ o : ↥H, π o = 1 ↔ o ∈ O := fun o => QuotientGroup.eq_one_iff (N := O) o
  have mem_M1 : ∀ x : Γ, x ∈ M1 ↔ ∃ h : x ∈ H, π ⟨x, h⟩ ∈ N₁ := by
    intro x
    change x ∈ (N₁.comap π).map H.subtype ↔ ∃ h : x ∈ H, π ⟨x, h⟩ ∈ N₁
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hπ⟩
      exact ⟨⟨x, hx⟩, hπ, rfl⟩
  have mem_M2 : ∀ x : Γ, x ∈ M2 ↔ ∃ h : x ∈ H, π ⟨x, h⟩ ∈ N₂ := by
    intro x
    change x ∈ (N₂.comap π).map H.subtype ↔ ∃ h : x ∈ H, π ⟨x, h⟩ ∈ N₂
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hπ⟩
      exact ⟨⟨x, hx⟩, hπ, rfl⟩
  have hle1 : M1 ≤ H := Subgroup.map_subtype_le c1
  have hle2 : M2 ≤ H := Subgroup.map_subtype_le c2
  have hO_c1 : O ≤ N₁.comap π := by
    intro o ho
    rw [Subgroup.mem_comap]
    rw [(hker o).mpr ho]
    exact N₁.one_mem
  have hO_c2 : O ≤ N₂.comap π := by
    intro o ho
    rw [Subgroup.mem_comap]
    rw [(hker o).mpr ho]
    exact N₂.one_mem
  have hp_le1 : P ≤ M1 := Subgroup.map_mono hO_c1
  have hp_le2 : P ≤ M2 := Subgroup.map_mono hO_c2
  have hcommP : ∀ a ∈ M1, ∀ b ∈ M2, a * b * a⁻¹ * b⁻¹ ∈ P := by
    intro a ha b hb
    rw [mem_M1 a] at ha
    rw [mem_M2 b] at hb
    obtain ⟨haH, haN⟩ := ha
    obtain ⟨hbH, hbN⟩ := hb
    let a' : ↥H := ⟨a, haH⟩
    let b' : ↥H := ⟨b, hbH⟩
    refine Subgroup.mem_map.mpr ⟨a' * b' * a'⁻¹ * b'⁻¹, ?_, ?_⟩
    · exact (hker _).mp (by
        simp only [map_mul, map_inv]
        rw [hcomm (π a') haN (π b') hbN]
        group)
    · rfl
  have hinfP : M1 ⊓ M2 ≤ P := by
    intro x hx
    rw [Subgroup.mem_inf] at hx
    rw [mem_M1 x] at hx
    rw [mem_M2 x] at hx
    obtain ⟨⟨hxH1, hπ1⟩, hxH2, hπ2⟩ := hx
    have hdisj' : N₁ ⊓ N₂ = ⊥ := disjoint_iff.mp hdisj
    have hmem : π (⟨x, hxH1⟩ : ↥H) ∈ N₁ ⊓ N₂ := by
      refine Subgroup.mem_inf.mpr ⟨hπ1, ?_⟩
      rw [show (⟨x, hxH1⟩ : ↥H) = ⟨x, hxH2⟩ from Subtype.ext rfl]
      exact hπ2
    have h1 : π (⟨x, hxH1⟩ : ↥H) = 1 := by
      rw [hdisj'] at hmem
      exact Subgroup.mem_bot.mp hmem
    exact Subgroup.mem_map.mpr ⟨⟨x, hxH1⟩, (hker _).mp h1, rfl⟩
  have hq2 : q * q = 1 := by
    have h : (⟨u, hu⟩ : ↥H) * ⟨u, hu⟩ = 1 := Subtype.ext (by simpa using hu2)
    have hpq : π ((⟨u, hu⟩ : ↥H) * ⟨u, hu⟩) = q * q := by
      rw [map_mul]
      rfl
    rw [← hpq, h, map_one]
  have hqinv : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq2
  have hconjπ : ∀ y : ↥H, π (⟨u, hu⟩ * y * ⟨u, hu⟩⁻¹) = q * π y * q⁻¹ := by
    intro y
    simp only [map_mul, map_inv]
    rfl
  have hconj' : N₁.map (MulAut.conj q).toMonoidHom = N₂ := by
    simpa [q, O] using hconj
  have hswap1 : ∀ a ∈ M1, u * a * u⁻¹ ∈ M2 := by
    intro a ha
    rw [mem_M1 a] at ha
    obtain ⟨haH, haN⟩ := ha
    let a' : ↥H := ⟨a, haH⟩
    let w : ↥H := ⟨u, hu⟩ * a' * ⟨u, hu⟩⁻¹
    have hwN : π w ∈ N₂ := by
      have hmem : π w ∈ N₁.map (MulAut.conj q).toMonoidHom := by
        refine Subgroup.mem_map.mpr ⟨π a', haN, ?_⟩
        exact (hconjπ a').symm
      rwa [hconj'] at hmem
    exact Subgroup.mem_map.mpr ⟨w, Subgroup.mem_comap.mpr hwN, rfl⟩
  have hswap2 : ∀ a ∈ M2, u * a * u⁻¹ ∈ M1 := by
    intro a ha
    rw [mem_M2 a] at ha
    obtain ⟨haH, haN⟩ := ha
    let a' : ↥H := ⟨a, haH⟩
    let w : ↥H := ⟨u, hu⟩ * a' * ⟨u, hu⟩⁻¹
    have hwN : π w ∈ N₁ := by
      have hmem : π a' ∈ N₁.map (MulAut.conj q).toMonoidHom := by
        rw [hconj']
        exact haN
      obtain ⟨y, hyN₁, hyeq⟩ := Subgroup.mem_map.mp hmem
      have hyeq' : q * y * q⁻¹ = π a' := hyeq
      have hqconj : q * π a' * q⁻¹ = y := by
        calc q * π a' * q⁻¹ = q * (q * y * q⁻¹) * q⁻¹ := by rw [← hyeq']
          _ = (q * q) * y * (q⁻¹ * q⁻¹) := by group
          _ = y := by rw [hq2, hqinv, hq2, one_mul, mul_one]
      have h1 : π w = q * π a' * q⁻¹ := hconjπ a'
      rw [h1, hqconj]
      exact hyN₁
    exact Subgroup.mem_map.mpr ⟨w, Subgroup.mem_comap.mpr hwN, rfl⟩
  let M : Subgroup Γ := M1 ⊔ M2 ⊔ zpowers u
  let M' : Subgroup ↥H := M.comap H.subtype
  have hO_M' : O ≤ M' := by
    intro o ho
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left
      (hp_le1 (Subgroup.mem_map.mpr ⟨o, ho, rfl⟩)))
  have hq_M' : (⟨u, hu⟩ : ↥H) ∈ M' := by
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hD_le : (N₁ ⊔ N₂ ⊔ zpowers q) ≤ M'.map π := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro n hn
      obtain ⟨n', hn'⟩ := QuotientGroup.mk'_surjective (N := O) n
      refine Subgroup.mem_map.mpr ⟨n', ?_, hn'⟩
      rw [Subgroup.mem_comap]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_left
        (Subgroup.mem_map.mpr ⟨n', Subgroup.mem_comap.mpr (by rw [hn']; exact hn), rfl⟩))
    · intro n hn
      obtain ⟨n', hn'⟩ := QuotientGroup.mk'_surjective (N := O) n
      refine Subgroup.mem_map.mpr ⟨n', ?_, hn'⟩
      rw [Subgroup.mem_comap]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_right
        (Subgroup.mem_map.mpr ⟨n', Subgroup.mem_comap.mpr (by rw [hn']; exact hn), rfl⟩))
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_map.mpr ⟨⟨u, hu⟩, hq_M', rfl⟩
  have hDtop : (N₁ ⊔ N₂ ⊔ zpowers q) = ⊤ := by
    have hDdvd := Subgroup.index_dvd_of_le (le_sup_left : N₁ ⊔ N₂ ≤ N₁ ⊔ N₂ ⊔ zpowers q)
    rw [hidx] at hDdvd
    have hle2 : (N₁ ⊔ N₂ ⊔ zpowers q).index ≤ 2 := Nat.le_of_dvd (by norm_num) hDdvd
    have hpos : 0 < (N₁ ⊔ N₂ ⊔ zpowers q).index :=
      Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := N₁ ⊔ N₂ ⊔ zpowers q))
    have hcases : (N₁ ⊔ N₂ ⊔ zpowers q).index = 1 ∨
        (N₁ ⊔ N₂ ⊔ zpowers q).index = 2 := by omega
    rcases hcases with h | h
    · exact Subgroup.index_eq_one.mp h
    · exfalso
      have hcardeq : Nat.card ↥(N₁ ⊔ N₂ ⊔ zpowers q) = Nat.card ↥(N₁ ⊔ N₂) := by
        have h1 := Subgroup.card_mul_index (N₁ ⊔ N₂ ⊔ zpowers q)
        have h2 := Subgroup.card_mul_index (N₁ ⊔ N₂)
        rw [h] at h1
        rw [hidx] at h2
        omega
      have heq : N₁ ⊔ N₂ = N₁ ⊔ N₂ ⊔ zpowers q :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (le_of_eq hcardeq)
      have hqD : q ∈ N₁ ⊔ N₂ ⊔ zpowers q :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers q)
      rw [← heq] at hqD
      exact hnot hqD
  have hsup : M1 ⊔ M2 ⊔ zpowers u = H := by
    apply le_antisymm
    · exact sup_le (sup_le hle1 hle2) (Subgroup.zpowers_le.mpr hu)
    · intro h hh
      let h' : ↥H := ⟨h, hh⟩
      have hmemD : π h' ∈ N₁ ⊔ N₂ ⊔ zpowers q := by rw [hDtop]; exact Subgroup.mem_top _
      obtain ⟨m', hm'M, hm'eq⟩ := Subgroup.mem_map.mp (hD_le hmemD)
      have hO : h' * m'⁻¹ ∈ O := (hker _).mp (by
        simp only [map_mul, map_inv]
        rw [hm'eq]
        group)
      have hm1 : h' * m'⁻¹ ∈ M' := hO_M' hO
      have heq : h' = (h' * m'⁻¹) * m' := by group
      have : h' ∈ M' := by rw [heq]; exact M'.mul_mem hm1 hm'M
      exact Subgroup.mem_comap.mp this
  have hu_not : u ∉ M1 ⊔ M2 := by
    intro huM
    have hle : M1 ⊔ M2 ≤ ((N₁ ⊔ N₂).comap π).map H.subtype :=
      sup_le (Subgroup.map_mono (Subgroup.comap_mono le_sup_left))
        (Subgroup.map_mono (Subgroup.comap_mono le_sup_right))
    obtain ⟨x', hx'N, hx'eq⟩ := Subgroup.mem_map.mp (hle huM)
    have hx' : x' = (⟨u, hu⟩ : ↥H) := Subtype.ext (by simpa using hx'eq)
    have hthis : (QuotientGroup.mk (⟨u, hu⟩ : ↥H) : ↥H ⧸ fusionOddCore ↥H) ∈ N₁ ⊔ N₂ := by
      change π (⟨u, hu⟩ : ↥H) ∈ N₁ ⊔ N₂
      rw [← hx']
      exact hx'N
    exact hnot hthis
  have hquot1 : QuotEquivTo M1 P (alternatingGroup (Fin 6)) := by
    obtain ⟨e⟩ := hN₁
    exact quotEquivTo_map_comap H O N₁ e
  have hquot2 : QuotEquivTo M2 P (alternatingGroup (Fin 6)) := by
    obtain ⟨e⟩ := hN₂
    exact quotEquivTo_map_comap H O N₂ e
  refine ⟨M1, M2, ?_⟩
  change WreathMod H P M1 M2 u
  exact ⟨hp_le1, hp_le2, hle1, hle2, hcommP, hinfP, hsup, hu_not, hswap1, hswap2,
    hquot1, hquot2⟩

end C10

end CFSG.OddStandard.SmallF3.Omega
