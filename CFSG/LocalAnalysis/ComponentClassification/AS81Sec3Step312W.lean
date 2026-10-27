module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step38Rho
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step312Lin
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
open CFSG.ComponentClassification.AschbacherTightEmbedding

section General

variable {G : Type} [Group G]

theorem mem_centerIn_rightConjugate_iff (H : Subgroup G) (g x : G) :
    x ∈ centerIn (rightConjugate H g) ↔ g * x * g⁻¹ ∈ centerIn H := by
  simp only [centerIn, mem_inf, mem_rightConjugate_iff, SetLike.mem_coe, mem_centralizer_iff]
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨hx, fun y hy => ?_⟩
    have h := hc (g⁻¹ * y * g) (by rw [show g * (g⁻¹ * y * g) * g⁻¹ = y by group]; exact hy)
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * y := by group
  · rintro ⟨hx, hc⟩
    refine ⟨hx, fun y hy => ?_⟩
    have h := hc (g * y * g⁻¹) hy
    calc y * x = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by rw [h]
      _ = x * y := by group

variable [Finite G]

theorem Sec312.exists_mem_normalizer_of_lt
    {S H : Subgroup G} (hS : IsPGroup 2 S) (hHS : H ≤ S) (hne : H ≠ S) :
    ∃ x ∈ S, x ∈ normalizer (H : Set G) ∧ x ∉ H := by
  have : Group.IsNilpotent S := hS.isNilpotent
  have hlt : H.subgroupOf S < ⊤ :=
    lt_top_iff_ne_top.2 fun h => hne (le_antisymm hHS (Subgroup.subgroupOf_eq_top.1 h))
  obtain ⟨x, hx, hxn⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  refine ⟨x, x.2, ?_, hxn⟩
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro h
  constructor
  · intro hh
    have := (hx ⟨h, hHS hh⟩).1 (by simpa [Subgroup.mem_subgroupOf] using hh)
    simpa [Subgroup.mem_subgroupOf] using this
  · intro hh
    have hhS : h ∈ S := by
      have : (x : G)⁻¹ * (x * h * x⁻¹) * x ∈ S :=
        S.mul_mem (S.mul_mem (S.inv_mem x.2) (hHS hh)) x.2
      simpa [mul_assoc] using this
    have := (hx ⟨h, hhS⟩).2 (by simpa [Subgroup.mem_subgroupOf] using hh)
    simpa [Subgroup.mem_subgroupOf] using this

end General

namespace XSub

variable {G : Type} [Group G] [Finite G] (D : XSub G)

theorem exists_involution_of_card_le {X : Subgroup G} (hX : X ≤ D.Q₁) (h16 : 16 ≤ Nat.card X) :
    ∃ a ∈ X, a * a = 1 ∧ a ∉ zpowers D.z := by
  have hle : X ≤ D.clPre (D.clSub X) := fun a ha => ⟨hX ha, D.cl_mem_clSub ha (hX ha)⟩
  have h1 := Subgroup.card_le_of_le hle
  rw [D.card_clPre] at h1
  by_contra hcon
  push Not at hcon
  have haniso : ∀ w ∈ D.clSub X, D.q w = 0 → w = 0 := fun w hw hq => by
    obtain ⟨a, haX, haQ, rfl⟩ := D.mem_clSub_iff.mp hw
    have ha2 : a ^ 2 = 1 := (D.q_cl_eq_zero_iff haQ).mp hq
    exact (D.cl_eq_zero_iff haQ).mpr (hcon a haX (by rw [← _root_.sq]; exact ha2))
  have h4 := Sec312.card_le_four_of_aniso haniso
  omega

theorem two_le_pRank_of_mem {H : Subgroup G} {a : G} (haQ : a ∈ D.Q₁) (haH : a ∈ H)
    (hzH : D.z ∈ H) (ha : a * a = 1) (haz : a ∉ zpowers D.z) : 2 ≤ Open.pRank 2 H := by
  have hv : D.cl a ≠ 0 := fun h => haz ((D.cl_eq_zero_iff haQ).mp h)
  have hqa : D.q (D.cl a) = 0 := (D.q_cl_eq_zero_iff haQ).mpr (by rw [_root_.sq]; exact ha)
  set L := Submodule.span (ZMod 2) {D.cl a}
  have hmemL : ∀ w ∈ L, w = 0 ∨ w = D.cl a := by
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rcases Sec312.zmod2_eq_zero_or_one c with rfl | rfl
    · exact Or.inl (zero_smul _ _)
    · exact Or.inr (one_smul _ _)
  have hE : D.clPre L ≤ H := by
    intro x hx
    rcases hmemL _ hx.2 with h0 | h1
    · exact (zpowers_le.mpr hzH) ((D.cl_eq_zero_iff hx.1).mp h0)
    · have h2 := (D.cl_eq_cl_iff haQ hx.1).mp h1.symm
      rw [show x = a * (a⁻¹ * x) by group]
      exact H.mul_mem haH ((zpowers_le.mpr hzH) h2)
  have hel : Open.IsElemAbelian 2 (D.clPre L) := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · have hp : polar D.q (D.cl x) (D.cl y) = 0 := by
        rcases hmemL _ x.2.2 with h0 | h0 <;> rcases hmemL _ y.2.2 with h1 | h1 <;>
          rw [h0, h1] <;> simp [polar_self, hqa]
      exact (D.polar_cl_eq_zero_iff x.2.1 y.2.1).mp hp
    · have hq : D.q (D.cl x) = 0 := by
        rcases hmemL _ hx.2 with h0 | h0 <;> rw [h0]
        · exact map_zero _
        · exact hqa
      exact (D.q_cl_eq_zero_iff hx.1).mp hq
  have hcard : Nat.card (D.clPre L) = 2 ^ 2 := by
    rw [D.card_clPre, D.card_submodule, finrank_span_singleton hv]
    norm_num
  exact CFSG.SectionRank.le_pRank one_lt_two hE hel hcard

omit [Finite G] in
theorem conj_eq_of_mem_zpowers {g : G} (hg : g ∈ centralizer ({D.z} : Set G)) {x : G}
    (hx : x ∈ zpowers D.z) : g * x * g⁻¹ = x := by
  rcases D.mem_zpowers_z_iff.mp hx with rfl | rfl
  · group
  · rw [mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]

@[expose] noncomputable def conj (g : G) (hg : g ∈ centralizer ({D.z} : Set G)) : XSub G where
  Q₁ := rightConjugate D.Q₁ g
  z := D.z
  extraspecial := CFSG.RankThree.PartOne.Torsion37.isExtraspecialPGroup_of_mulEquiv
    (Subgroup.equivMapOfInjective D.Q₁ (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective) D.extraspecial
  center_eq := by
    ext x
    rw [mem_centerIn_rightConjugate_iff, D.center_eq]
    constructor
    · intro h
      have e := D.conj_eq_of_mem_zpowers hg h
      have e2 : x = g * x * g⁻¹ := by
        calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = g⁻¹ * (g * (g * x * g⁻¹) * g⁻¹) * g := by rw [e]
          _ = g * x * g⁻¹ := by group
      rw [e2]
      exact h
    · intro h
      rw [D.conj_eq_of_mem_zpowers hg h]
      exact h

omit [Finite G] in
theorem le_zpowers_of_le_centralizer_conj
    (hC : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ centralizer (D.Q₁ : Set G) → S ≤ zpowers D.z)
    {g : G} (hg : g ∈ centralizer ({D.z} : Set G)) {S : Subgroup G} (hS : IsPGroup 2 S)
    (hSC : S ≤ centralizer (rightConjugate D.Q₁ g : Set G)) : S ≤ zpowers D.z := by
  intro s hs
  have hS' : S.map (MulAut.conj g).toMonoidHom ≤ zpowers D.z := by
    refine hC _ (hS.map _) ?_
    rintro _ ⟨t, ht, rfl⟩
    rw [mem_centralizer_iff]
    intro y hy
    have hy' : g⁻¹ * y * g ∈ rightConjugate D.Q₁ g := by
      rw [mem_rightConjugate_iff]
      group
      exact hy
    have h := mem_centralizer_iff.mp (hSC ht) _ hy'
    show y * (g * t * g⁻¹) = g * t * g⁻¹ * y
    calc y * (g * t * g⁻¹) = g * ((g⁻¹ * y * g) * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = g * t * g⁻¹ * y := by group
  have h1 : g * s * g⁻¹ ∈ zpowers D.z := hS' ⟨s, hs, rfl⟩
  have e := D.conj_eq_of_mem_zpowers hg h1
  have e2 : s = g * s * g⁻¹ := by
    calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
      _ = g⁻¹ * (g * (g * s * g⁻¹) * g⁻¹) * g := by rw [e]
      _ = g * s * g⁻¹ := by group
  rw [e2]
  exact h1

theorem card_inf_normalizer_le
    (hC : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ centralizer (D.Q₁ : Set G) → S ≤ zpowers D.z)
    {g : G} (hg : g ∈ centralizer ({D.z} : Set G)) (hPN : rightConjugate D.Q₁ g ≤ D.N)
    {T : Subgroup G} (hT : IsPGroup 2 T) (hQT : D.Q₁ ≤ T) (hPT : rightConjugate D.Q₁ g ≤ T)
    (h1 : ∀ a ∈ D.Q₁ ⊓ rightConjugate D.Q₁ g, a * a = 1 → a ∈ zpowers D.z) :
    Nat.card ↥(D.Q₁ ⊓ normalizer (rightConjugate D.Q₁ g : Set G)) ≤
      2 * Nat.card ↥(D.Q₁ ⊓ rightConjugate D.Q₁ g) := by
  set P := rightConjugate D.Q₁ g with hPdef
  let D' := D.conj g hg
  have hD'Q : D'.Q₁ = P := rfl
  have hD'z : D'.z = D.z := rfl
  set N₀ := D.Q₁ ⊓ normalizer (P : Set G)
  have hN₀ : N₀ ≤ D'.N := inf_le_right
  let ψ : ↥N₀ →* D'.O := D'.ρ.comp (Subgroup.inclusion hN₀)
  have hcard := Subgroup.card_ker_mul_card_range ψ
  have hker : Nat.card ψ.ker ≤ Nat.card ↥(D.Q₁ ⊓ P) := by
    have hle : ψ.ker.map N₀.subtype ≤ D.Q₁ ⊓ P := by
      rintro _ ⟨n, hn, rfl⟩
      have hn1 : D'.ρ (Subgroup.inclusion hN₀ n) = 1 := hn
      obtain ⟨c, hc, hcn⟩ := (D'.ρ_eq_one_iff _).mp hn1
      have hnQ : (n : G) ∈ D.Q₁ := (mem_inf.mp n.2).1
      have hcT : c⁻¹ * (n : G) ∈ T := T.mul_mem (T.inv_mem (hPT hc)) (hQT hnQ)
      have hz : c⁻¹ * (n : G) ∈ zpowers D.z :=
        D.le_zpowers_of_le_centralizer_conj hC hg (hT.to_le (zpowers_le.mpr hcT))
          (zpowers_le.mpr hcn) (mem_zpowers _)
      refine mem_inf.mpr ⟨hnQ, ?_⟩
      show (n : G) ∈ P
      rw [show (n : G) = c * (c⁻¹ * n) by group]
      exact P.mul_mem hc ((zpowers_le.mpr D'.z_mem) hz)
    calc Nat.card ψ.ker = Nat.card (ψ.ker.map N₀.subtype) :=
          (card_map_of_injective N₀.subtype_injective).symm
      _ ≤ _ := Subgroup.card_le_of_le hle
  have hrange : Nat.card ψ.range ≤ 2 := by
    let W := D'.clSub (D.Q₁ ⊓ P)
    have haniso : ∀ w ∈ W, D'.q w = 0 → w = 0 := fun w hw hq =>
      D'.eq_zero_of_q_eq_zero (fun a ha _ ha2 => h1 a ha (by rw [← _root_.sq]; exact ha2)) hw hq
    let H : Subgroup (D'.Qt ≃ₗ[ZMod 2] D'.Qt) := ψ.range.map D'.O.subtype
    have hiso : ∀ t ∈ H, ∀ v, D'.q (t v) = D'.q v := by
      rintro _ ⟨m, -, rfl⟩ v
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp m.2 v
    have hcomm : ∀ n : ↥N₀, ∀ a ∈ P, (n : G) * a * (n : G)⁻¹ * a⁻¹ ∈ D.Q₁ ⊓ P := by
      intro n a ha
      have hnQ : (n : G) ∈ D.Q₁ := (mem_inf.mp n.2).1
      have hnN : (n : G) ∈ normalizer (P : Set G) := (mem_inf.mp n.2).2
      refine mem_inf.mpr ⟨?_, ?_⟩
      · have h2 : a * (n : G)⁻¹ * a⁻¹ ∈ D.Q₁ := D.conj_mem (hPN ha) (inv_mem hnQ)
        rw [show (n : G) * a * (n : G)⁻¹ * a⁻¹ = n * (a * (n : G)⁻¹ * a⁻¹) by group]
        exact mul_mem hnQ h2
      · exact mul_mem ((mem_normalizer_iff.mp hnN a).mp ha) (inv_mem ha)
    have hrng : ∀ t ∈ H, ∀ v, t v - v ∈ W := by
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩ v
      obtain ⟨a, ha, rfl⟩ := D'.exists_cl v
      have ha' : a ∈ P := ha
      show ((D'.ρ (Subgroup.inclusion hN₀ n) : D'.O) : D'.Qt ≃ₗ[ZMod 2] D'.Qt) (D'.cl a) -
        D'.cl a ∈ W
      rw [D'.ρ_cl _ ha]
      have hmem := hcomm n a ha'
      have hna : (n : G) * a * (n : G)⁻¹ ∈ D'.Q₁ := D'.conj_mem (hN₀ n.2) ha
      have e : D'.cl ((n : G) * a * (n : G)⁻¹) - D'.cl a =
          D'.cl ((n : G) * a * (n : G)⁻¹ * a⁻¹) := by
        rw [D'.cl_mul hna (inv_mem ha), D'.cl_inv ha, sub_eq_add_neg, ZModModule.neg_eq_self]
      rw [show ((Subgroup.inclusion hN₀ n : D'.N) : G) = (n : G) from rfl, e]
      exact D'.cl_mem_clSub hmem (mem_inf.mp hmem).2
    have hfix : ∀ t ∈ H, ∀ w ∈ W, t w = w := by
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩ w hw
      obtain ⟨d, hdX, hdQ, rfl⟩ := D'.mem_clSub_iff.mp hw
      show ((D'.ρ (Subgroup.inclusion hN₀ n) : D'.O) : D'.Qt ≃ₗ[ZMod 2] D'.Qt) (D'.cl d) =
        D'.cl d
      rw [D'.ρ_cl _ hdQ]
      have hnQ : (n : G) ∈ D.Q₁ := (mem_inf.mp n.2).1
      have hdQ₁ : d ∈ D.Q₁ := (mem_inf.mp hdX).1
      have hnd : (n : G) * d * (n : G)⁻¹ ∈ D'.Q₁ := D'.conj_mem (hN₀ n.2) hdQ
      rw [show ((Subgroup.inclusion hN₀ n : D'.N) : G) = (n : G) from rfl]
      refine ((D'.cl_eq_cl_iff hnd hdQ).mpr ?_)
      show _ ∈ zpowers D.z
      have hQ : ((n : G) * d * (n : G)⁻¹)⁻¹ * d ∈ D.Q₁ :=
        mul_mem (inv_mem (D.conj_mem (D.le_N hnQ) hdQ₁)) hdQ₁
      rw [← D.cl_eq_zero_iff hQ, D.cl_mul (inv_mem (D.conj_mem (D.le_N hnQ) hdQ₁)) hdQ₁,
        D.cl_inv (D.conj_mem (D.le_N hnQ) hdQ₁), D.cl_mul (mul_mem hnQ hdQ₁) (inv_mem hnQ),
        D.cl_mul hnQ hdQ₁, D.cl_inv hnQ]
      rw [add_assoc (D.cl (n : G) + D.cl d), ZModModule.add_self]
    have hH := Sec312.card_le_two_of_aniso haniso H hiso hrng hfix
    rwa [show Nat.card H = Nat.card ψ.range from
      card_map_of_injective D'.O.subtype_injective] at hH
  calc Nat.card ↥N₀ = Nat.card ψ.ker * Nat.card ψ.range := hcard.symm
    _ ≤ Nat.card ↥(D.Q₁ ⊓ P) * 2 := Nat.mul_le_mul hker hrange
    _ = 2 * Nat.card ↥(D.Q₁ ⊓ P) := mul_comm _ _

theorem eq_of_rightConjugate_le_N
    (hC : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ centralizer (D.Q₁ : Set G) → S ≤ zpowers D.z)
    (h9 : Nat.card D.Q₁ = 2 ^ 9)
    (hi : ∀ h ∈ centralizer ({D.z} : Set G),
      1 < Open.pRank 2 (D.Q₁ ⊓ rightConjugate D.Q₁ h) → rightConjugate D.Q₁ h = D.Q₁)
    {g : G} (hg : g ∈ centralizer ({D.z} : Set G)) (hPN : rightConjugate D.Q₁ g ≤ D.N)
    {T : Subgroup G} (hT : IsPGroup 2 T) (hQT : D.Q₁ ≤ T) (hPT : rightConjugate D.Q₁ g ≤ T) :
    rightConjugate D.Q₁ g = D.Q₁ := by
  classical
  by_contra hne
  set P := rightConjugate D.Q₁ g with hPdef
  have hzP : D.z ∈ P := (D.conj g hg).z_mem
  have hzQP : D.z ∈ D.Q₁ ⊓ P := mem_inf.mpr ⟨D.z_mem, hzP⟩
  have h1 : ∀ a ∈ D.Q₁ ⊓ P, a * a = 1 → a ∈ zpowers D.z := by
    intro a ha ha2
    by_contra haz
    exact hne (hi g hg (D.two_le_pRank_of_mem (mem_inf.mp ha).1 ha hzQP ha2 haz))
  have hD₀ : Nat.card ↥(D.Q₁ ⊓ P) ≤ 8 := by
    have hle : D.Q₁ ⊓ P ≤ D.clPre (D.clSub (D.Q₁ ⊓ P)) := fun a ha =>
      ⟨(mem_inf.mp ha).1, D.cl_mem_clSub ha (mem_inf.mp ha).1⟩
    have h4 := Sec312.card_le_four_of_aniso (Q := D.q) (W := D.clSub (D.Q₁ ⊓ P))
      fun w hw hq => D.eq_zero_of_q_eq_zero
        (fun a ha _ ha2 => h1 a ha (by rw [← _root_.sq]; exact ha2)) hw hq
    have h5 := Subgroup.card_le_of_le hle
    rw [D.card_clPre] at h5
    omega
  set N₀ := D.Q₁ ⊓ normalizer (P : Set G) with hN₀def
  have hN₀ : Nat.card ↥N₀ ≤ 16 := by
    have h := D.card_inf_normalizer_le hC hg hPN hT hQT hPT h1
    change Nat.card ↥N₀ ≤ 2 * Nat.card ↥(D.Q₁ ⊓ P) at h
    omega
  have hzN₀ : D.z ∈ N₀ := mem_inf.mpr ⟨D.z_mem, le_normalizer hzP⟩
  set U := D.clSub N₀ with hUdef
  have hU : Nat.card U ≤ 8 := by
    have h := D.card_clPre U
    have e : D.clPre U = N₀ := D.clPre_clSub inf_le_left hzN₀
    rw [e] at h
    omega
  let act : ↥P →* (D.Qt ≃ₗ[ZMod 2] D.Qt) :=
    D.O.subtype.comp (D.ρ.comp (Subgroup.inclusion hPN))
  have hact : ∀ (a : ↥P) {x : G}, x ∈ D.Q₁ →
      act a (D.cl x) = D.cl ((a : G) * x * (a : G)⁻¹) := fun a x hx =>
    D.ρ_cl (Subgroup.inclusion hPN a) hx
  have hN₀conj : ∀ a ∈ P, ∀ x ∈ N₀, a * x * a⁻¹ ∈ N₀ := by
    intro a ha x hx
    refine mem_inf.mpr ⟨D.conj_mem (hPN ha) (mem_inf.mp hx).1, ?_⟩
    exact mul_mem (mul_mem (le_normalizer ha) (mem_inf.mp hx).2) (inv_mem (le_normalizer ha))
  have hUinv : ∀ a : ↥P, U.map (act a : D.Qt →ₗ[ZMod 2] D.Qt) = U := by
    intro a
    have h := D.map_ρ_clSub (Subgroup.inclusion hPN a) N₀
    change (D.clSub N₀).map (act a : D.Qt →ₗ[ZMod 2] D.Qt) =
      D.clSub (N₀.map (MulAut.conj (a : G)).toMonoidHom) at h
    have hmap : N₀.map (MulAut.conj (a : G)).toMonoidHom = N₀ := by
      refine le_antisymm ?_ fun x hx => ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact hN₀conj a a.2 x hx
      · refine ⟨(a : G)⁻¹ * x * (a : G)⁻¹⁻¹, hN₀conj _ (inv_mem a.2) x hx, ?_⟩
        show (a : G) * ((a : G)⁻¹ * x * (a : G)⁻¹⁻¹) * (a : G)⁻¹ = x
        group
    rw [hmap] at h
    exact h
  have hQt : Nat.card D.Qt = 2 ^ 8 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, D.finrank_Qt h9]
  have hP2 : IsPGroup 2 ↥P := hT.to_le hPT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hvU, hvfix⟩ : ∃ v : D.Qt, v ∉ U ∧ ∀ a : ↥P, act a v - v ∈ U := by
    have hUle : ∀ a : ↥P, U ≤ U.comap (act a : D.Qt →ₗ[ZMod 2] D.Qt) := fun a =>
      Submodule.map_le_iff_le_comap.mp (hUinv a).le
    let σ : ↥P →* Module.End (ZMod 2) (D.Qt ⧸ U) :=
      { toFun := fun a => U.mapQ U (act a : D.Qt →ₗ[ZMod 2] D.Qt) (hUle a)
        map_one' := by
          apply Submodule.linearMap_qext
          ext w
          simp
        map_mul' := fun a b => by
          apply Submodule.linearMap_qext
          ext w
          simp [map_mul] }
    let _ : MulAction ↥P (D.Qt ⧸ U) := MulAction.compHom _ σ
    have : Finite D.Qt := Module.finite_of_finite (ZMod 2)
    have : Finite (D.Qt ⧸ U) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective U)
    have hmod := hP2.card_modEq_card_fixedPoints (D.Qt ⧸ U)
    have hcq := Submodule.card_eq_card_quotient_mul_card U
    rw [hQt] at hcq
    have hdvd : Nat.card (D.Qt ⧸ U) ∣ 2 ^ 8 := Dvd.intro_left _ hcq.symm
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hUpos : 0 < Nat.card U := Nat.card_pos
    have hk1 : 1 ≤ k := by
      by_contra h0
      have : k = 0 := by omega
      rw [this, pow_zero] at hk'
      rw [hk', mul_one] at hcq
      omega
    have heven : 2 ∣ Nat.card (D.Qt ⧸ U) := by
      rw [hk']
      exact dvd_pow_self 2 (by omega)
    have hfix2 : 2 ∣ Nat.card (MulAction.fixedPoints ↥P (D.Qt ⧸ U)) :=
      (Nat.modEq_zero_iff_dvd.mp ((hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr heven))))
    have h0fix : (0 : D.Qt ⧸ U) ∈ MulAction.fixedPoints ↥P (D.Qt ⧸ U) := fun a =>
      show σ a 0 = 0 from map_zero _
    obtain ⟨x, hx, hx0⟩ : ∃ x ∈ MulAction.fixedPoints ↥P (D.Qt ⧸ U), x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hsub : MulAction.fixedPoints ↥P (D.Qt ⧸ U) ⊆ {0} := fun x hx => hcon x hx
      have h1 := Set.ncard_le_ncard hsub (Set.finite_singleton _)
      rw [Set.ncard_singleton, ← Nat.card_coe_set_eq] at h1
      have h2 : 0 < Nat.card (MulAction.fixedPoints ↥P (D.Qt ⧸ U)) :=
        Nat.card_pos_iff.mpr ⟨⟨_, h0fix⟩, inferInstance⟩
      obtain ⟨m, hm⟩ := hfix2
      omega
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective U x
    refine ⟨v, fun h => hx0 ((Submodule.Quotient.mk_eq_zero U).mpr h), fun a => ?_⟩
    have h := hx a
    change σ a (Submodule.Quotient.mk v) = Submodule.Quotient.mk v at h
    rw [show σ a (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (act a v) from Submodule.mapQ_apply U U _ (h := hUle a) v] at h
    exact (Submodule.Quotient.eq U).mp h
  obtain ⟨b, hbQ, rfl⟩ := D.exists_cl v
  let _ : MulAction ↥P D.Qt := MulAction.compHom _ act
  have horb : (MulAction.orbit ↥P (D.cl b)).ncard ≤ Nat.card U := by
    have hsub : MulAction.orbit ↥P (D.cl b) ⊆ (fun u => D.cl b + u) '' (U : Set D.Qt) := by
      rintro _ ⟨a, rfl⟩
      refine ⟨act a (D.cl b) - D.cl b, hvfix a, ?_⟩
      show D.cl b + (act a (D.cl b) - D.cl b) = act a (D.cl b)
      rw [add_sub_cancel]
    calc _ ≤ ((fun u => D.cl b + u) '' (U : Set D.Qt)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ (U : Set D.Qt).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = Nat.card U := (Nat.card_coe_set_eq _).symm
  have hPc : Nat.card ↥P = 2 ^ 9 := by rw [hPdef, rightConjugate_card, h9]
  have hstab : 64 ≤ Nat.card (MulAction.stabilizer ↥P (D.cl b)) := by
    have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥P (D.cl b))
    rw [MulAction.index_stabilizer, hPc] at h1
    by_contra hlt
    push Not at hlt
    have h2 : Nat.card (MulAction.stabilizer ↥P (D.cl b)) *
        (MulAction.orbit ↥P (D.cl b)).ncard ≤ 63 * 8 :=
      Nat.mul_le_mul (by omega) (horb.trans hU)
    omega
  have hSv : (MulAction.stabilizer ↥P (D.cl b)).map P.subtype ≤ P ⊓ rightConjugate P b⁻¹ := by
    rintro _ ⟨a, ha, rfl⟩
    have ha' : act a (D.cl b) = D.cl b := ha
    rw [hact a hbQ] at ha'
    have hab := (D.cl_eq_cl_iff (D.conj_mem (hPN a.2) hbQ) hbQ).mp ha'
    refine mem_inf.mpr ⟨a.2, ?_⟩
    rw [mem_rightConjugate_iff, inv_inv]
    have e : b⁻¹ * (a : G) * b = (((a : G) * b * (a : G)⁻¹)⁻¹ * b)⁻¹ * a := by group
    show b⁻¹ * (a : G) * b ∈ P
    rw [e]
    exact mul_mem (inv_mem ((zpowers_le.mpr hzP) hab)) a.2
  have hbC : b ∈ centralizer ({D.z} : Set G) := mem_centralizer_singleton_iff.mpr (D.z_comm hbQ)
  have hh : g * b⁻¹ * g⁻¹ ∈ centralizer ({D.z} : Set G) :=
    mul_mem (mul_mem hg (inv_mem hbC)) (inv_mem hg)
  have hconj : rightConjugate (D.Q₁ ⊓ rightConjugate D.Q₁ (g * b⁻¹ * g⁻¹)) g =
      P ⊓ rightConjugate P b⁻¹ := by
    ext x
    simp only [hPdef, mem_inf, mem_rightConjugate_iff]
    rw [show g * b⁻¹ * g⁻¹ * (g * x * g⁻¹) * (g * b⁻¹ * g⁻¹)⁻¹ =
      g * (b⁻¹ * x * b⁻¹⁻¹) * g⁻¹ by group]
  have hcard16 : 16 ≤ Nat.card ↥(D.Q₁ ⊓ rightConjugate D.Q₁ (g * b⁻¹ * g⁻¹)) := by
    rw [← rightConjugate_card (D.Q₁ ⊓ rightConjugate D.Q₁ (g * b⁻¹ * g⁻¹)) g, hconj]
    have h1 := Subgroup.card_le_of_le hSv
    rw [card_map_of_injective P.subtype_injective] at h1
    omega
  have hrank : 1 < Open.pRank 2 (D.Q₁ ⊓ rightConjugate D.Q₁ (g * b⁻¹ * g⁻¹)) := by
    obtain ⟨a, ha, ha2, haz⟩ := D.exists_involution_of_card_le inf_le_left hcard16
    have hzX : D.z ∈ D.Q₁ ⊓ rightConjugate D.Q₁ (g * b⁻¹ * g⁻¹) :=
      mem_inf.mpr ⟨D.z_mem, (D.conj _ hh).z_mem⟩
    exact D.two_le_pRank_of_mem (mem_inf.mp ha).1 ha hzX ha2 haz
  have heq := hi _ hh hrank
  have hPb : rightConjugate P b⁻¹ = P := by
    have h1 := congrArg (fun X => rightConjugate X g) heq
    simp only [rightConjugate_mul] at h1
    rw [hPdef, rightConjugate_mul, ← h1, show g * b⁻¹ * g⁻¹ * g = g * b⁻¹ by group]
  have hbN : b ∈ normalizer (P : Set G) := by
    have h1 := (rightConjugate_eq_self_iff P b⁻¹).mp hPb
    simpa using inv_mem h1
  exact hvU (D.cl_mem_clSub (mem_inf.mpr ⟨hbQ, hbN⟩) hbQ)

omit [Finite G] in
theorem N_le_centralizer : D.N ≤ centralizer ({D.z} : Set G) := by
  intro n hn
  rw [mem_centralizer_singleton_iff]
  have h1 : n * D.z * n⁻¹ ∈ centerIn D.Q₁ := by
    refine ⟨D.conj_mem hn D.z_mem, mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hy' : n⁻¹ * y * n ∈ D.Q₁ := by simpa using D.conj_mem (inv_mem hn) hy
    have hc := D.z_comm hy'
    calc y * (n * D.z * n⁻¹) = n * ((n⁻¹ * y * n) * D.z) * n⁻¹ := by group
      _ = n * (D.z * (n⁻¹ * y * n)) * n⁻¹ := by rw [hc]
      _ = n * D.z * n⁻¹ * y := by group
  rw [D.center_eq] at h1
  rcases D.mem_zpowers_z_iff.mp h1 with h | h
  · exfalso
    apply D.z_ne_one
    calc D.z = n⁻¹ * (n * D.z * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  · calc n * D.z = n * D.z * n⁻¹ * n := by group
      _ = D.z * n := by rw [h]

theorem exists_isSylowOf_weaklyClosed
    (hC : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ centralizer (D.Q₁ : Set G) → S ≤ zpowers D.z)
    (h9 : Nat.card D.Q₁ = 2 ^ 9)
    (hi : ∀ h ∈ centralizer ({D.z} : Set G),
      1 < Open.pRank 2 (D.Q₁ ⊓ rightConjugate D.Q₁ h) → rightConjugate D.Q₁ h = D.Q₁) :
    ∃ T' : Subgroup G, ABGLocalTools.IsSylowOf 2 T' (centralizer ({D.z} : Set G)) ∧
      D.Q₁ ≤ T' ∧ ∀ h ∈ centralizer ({D.z} : Set G), rightConjugate D.Q₁ h ≤ T' →
        rightConjugate D.Q₁ h = D.Q₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀, hT₀⟩ := ABGLocalTools.exists_isSylowOf 2 D.N
  have hQT₀ : D.Q₁ ≤ T₀ := by
    have h2 : IsPGroup 2 (T₀ ⊔ D.Q₁ : Subgroup G) :=
      hT₀.isPGroup.to_sup_of_normal_right' D.extraspecial.1 hT₀.le
    have := hT₀.eq_of_le le_sup_left (sup_le hT₀.le D.le_N) h2
    rw [← this]
    exact le_sup_right
  set C := centralizer ({D.z} : Set G)
  have hT₀C : T₀ ≤ C := hT₀.le.trans D.N_le_centralizer
  have hwc : ∀ h ∈ C, rightConjugate D.Q₁ h ≤ T₀ → rightConjugate D.Q₁ h = D.Q₁ :=
    fun h hh hle => D.eq_of_rightConjugate_le_N hC h9 hi hh (hle.trans hT₀.le) hT₀.isPGroup
      hQT₀ hle
  refine ⟨T₀, ?_, hQT₀, hwc⟩
  obtain ⟨S, hS⟩ := (hT₀.isPGroup.comap_subtype (K := C)).exists_le_sylow
  have hT' : ABGLocalTools.IsSylowOf 2 ((S : Subgroup C).map C.subtype) C := ⟨S, rfl⟩
  have hT₀T' : T₀ ≤ (S : Subgroup C).map C.subtype := fun x hx =>
    ⟨⟨x, hT₀C hx⟩, hS hx, rfl⟩
  by_cases heq : T₀ = (S : Subgroup C).map C.subtype
  · rw [heq]
    exact hT'
  exfalso
  obtain ⟨t, htT', htN, htT₀⟩ :=
    Sec312.exists_mem_normalizer_of_lt hT'.isPGroup hT₀T' heq
  have htC : t ∈ C := hT'.le htT'
  have hQt : rightConjugate D.Q₁ t ≤ T₀ := by
    have h1 : rightConjugate T₀ t = T₀ := (rightConjugate_eq_self_iff T₀ t).mpr htN
    rw [← h1]
    intro x hx
    rw [mem_rightConjugate_iff] at hx ⊢
    exact hQT₀ hx
  have htNQ : t ∈ D.N := (rightConjugate_eq_self_iff D.Q₁ t).mp (hwc t htC hQt)
  have hle : T₀ ⊔ zpowers t ≤ (S : Subgroup C).map C.subtype :=
    sup_le hT₀T' (zpowers_le.mpr htT')
  have hsup := hT₀.eq_of_le le_sup_left (sup_le hT₀.le (zpowers_le.mpr htNQ))
    (hT'.isPGroup.to_le hle)
  exact htT₀ (hsup ▸ mem_sup_right (mem_zpowers t))

omit [Finite G] in
theorem comm_of_mem_zpowers {x c : G} (hx : x ∈ centralizer ({D.z} : Set G))
    (hc : c ∈ zpowers D.z) : x * c = c * x := by
  have h := D.conj_eq_of_mem_zpowers hx hc
  calc x * c = x * c * x⁻¹ * x := by group
    _ = c * x := by rw [h]

theorem eq_of_one_lt_pRank {s : G}
    (htrans : ∀ a ∈ D.Q₁, a * a = 1 → a ∉ zpowers D.z →
      ∃ f ∈ D.N, (f * a * f⁻¹)⁻¹ * s ∈ zpowers D.z)
    (hNs : ∀ n ∈ centralizer ({D.z} : Set G), n * s * n⁻¹ * s⁻¹ ∈ zpowers D.z → n ∈ D.N)
    (hsQ : s ∈ D.Q₁) {g : G} (hg : g ∈ centralizer ({D.z} : Set G))
    (hr : 1 < Open.pRank 2 (D.Q₁ ⊓ rightConjugate D.Q₁ g)) :
    rightConjugate D.Q₁ g = D.Q₁ := by
  classical
  obtain ⟨E, hEle, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two
    (D.Q₁ ⊓ rightConjugate D.Q₁ g)
  obtain ⟨a, haE, haz⟩ : ∃ a ∈ E, a ∉ zpowers D.z := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.card_le_of_le (show E ≤ zpowers D.z from hcon)
    rw [D.card_zpowers_z, hEcard] at h1
    have h2 : 2 ^ 2 ≤ 2 ^ Open.pRank 2 (D.Q₁ ⊓ rightConjugate D.Q₁ g) :=
      Nat.pow_le_pow_right (by norm_num) hr
    omega
  have ha2 : a * a = 1 := by rw [← _root_.sq]; exact hEel.2 a haE
  have haQ : a ∈ D.Q₁ := (mem_inf.mp (hEle haE)).1
  have haQg : g * a * g⁻¹ ∈ D.Q₁ := (mem_rightConjugate_iff _ _ _).mp (mem_inf.mp (hEle haE)).2
  have hga2 : (g * a * g⁻¹) * (g * a * g⁻¹) = 1 := by
    rw [show (g * a * g⁻¹) * (g * a * g⁻¹) = g * (a * a) * g⁻¹ by group, ha2]
    group
  have hgaz : g * a * g⁻¹ ∉ zpowers D.z := by
    intro h
    apply haz
    have e := D.conj_eq_of_mem_zpowers (inv_mem hg) h
    rw [show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a by group] at e
    rw [e]
    exact h
  obtain ⟨f₁, hf₁, hζ₁⟩ := htrans a haQ ha2 haz
  obtain ⟨f₂, hf₂, hζ₂⟩ := htrans _ haQg hga2 hgaz
  have hf₁C := D.N_le_centralizer hf₁
  have hf₂C := D.N_le_centralizer hf₂
  have hsC : s ∈ centralizer ({D.z} : Set G) := mem_centralizer_singleton_iff.mpr (D.z_comm hsQ)
  set ζ₁ := (f₁ * a * f₁⁻¹)⁻¹ * s
  set ζ₂ := (f₂ * (g * a * g⁻¹) * f₂⁻¹)⁻¹ * s
  have hn : (f₂ * g * f₁⁻¹) * s * (f₂ * g * f₁⁻¹)⁻¹ = s * (ζ₂⁻¹ * ζ₁) := by
    have e1 : s = f₁ * a * f₁⁻¹ * ζ₁ := by simp only [ζ₁]; group
    have e2 : f₂ * (g * a * g⁻¹) * f₂⁻¹ = s * ζ₂⁻¹ := by simp only [ζ₂]; group
    have c1 : f₁⁻¹ * ζ₁ * f₁ = ζ₁ := by
      have h := D.conj_eq_of_mem_zpowers (inv_mem hf₁C) hζ₁
      rwa [inv_inv] at h
    have c2 : (f₂ * g) * ζ₁ * (f₂ * g)⁻¹ = ζ₁ :=
      D.conj_eq_of_mem_zpowers (mul_mem hf₂C hg) hζ₁
    calc (f₂ * g * f₁⁻¹) * s * (f₂ * g * f₁⁻¹)⁻¹
        = (f₂ * g * f₁⁻¹) * (f₁ * a * f₁⁻¹ * ζ₁) * (f₂ * g * f₁⁻¹)⁻¹ := by rw [← e1]
      _ = f₂ * g * a * (f₁⁻¹ * ζ₁ * f₁) * g⁻¹ * f₂⁻¹ := by group
      _ = f₂ * g * a * ζ₁ * g⁻¹ * f₂⁻¹ := by rw [c1]
      _ = (f₂ * (g * a * g⁻¹) * f₂⁻¹) * ((f₂ * g) * ζ₁ * (f₂ * g)⁻¹) := by group
      _ = s * ζ₂⁻¹ * ζ₁ := by rw [e2, c2]
      _ = s * (ζ₂⁻¹ * ζ₁) := by group
  have hnC : f₂ * g * f₁⁻¹ ∈ centralizer ({D.z} : Set G) :=
    mul_mem (mul_mem hf₂C hg) (inv_mem hf₁C)
  have hnz : (f₂ * g * f₁⁻¹) * s * (f₂ * g * f₁⁻¹)⁻¹ * s⁻¹ ∈ zpowers D.z := by
    rw [hn]
    have hcz : ζ₂⁻¹ * ζ₁ ∈ zpowers D.z := mul_mem (inv_mem hζ₂) hζ₁
    have hc := D.comm_of_mem_zpowers hsC hcz
    rw [show s * (ζ₂⁻¹ * ζ₁) * s⁻¹ = (s * (ζ₂⁻¹ * ζ₁)) * s⁻¹ from rfl, hc]
    simpa using hcz
  have hnN := hNs _ hnC hnz
  have hgN : g ∈ D.N := by
    rw [show g = f₂⁻¹ * (f₂ * g * f₁⁻¹) * f₁ by group]
    exact mul_mem (mul_mem (inv_mem hf₂) hnN) hf₁
  exact (rightConjugate_eq_self_iff D.Q₁ g).mpr hgN

end XSub

end CFSG.ComponentClassification.AS81
