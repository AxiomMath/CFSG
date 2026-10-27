module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.YuBasic
public import CFSG.CGT.PushingUpLit.CGT6.Emb5Basic
public import CFSG.CGT.PushingUpLit.SolK.Block
public import CFSG.Quasithin.EmptyFaithful.S153E55A
public import CFSG.CGT.PushingUpLit.CGT6E.Emb55Conj

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.Quasithin.G6 CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

section Data

variable {V : Type} [CommGroup V]

structure AltBlock (B : Subgroup (MulAut V)) (n : ℕ) where
  θ : ↥B →* Equiv.Perm (Fin (2 * n + 1))
  θ_alt : ∀ b, θ b ∈ alternatingGroup (Fin (2 * n + 1))
  θ_surj : ∀ a ∈ alternatingGroup (Fin (2 * n + 1)), ∃ b, θ b = a
  β : ↥(commV B) ≃* ↥(coreMod (2 * n + 1))
  equivar : ∀ (b : ↥B) (e : ↥(commV B)),
    β ⟨(b : MulAut V) (e : V), apply_mem_commV_self B b.2 e.2⟩ = coreAct (2 * n + 1) (θ b) (β e)
  ker_central : ∀ b : ↥B, θ b = 1 → b ∈ Subgroup.center ↥B
  ker_two : ∀ b : ↥B, θ b = 1 → ∃ k : ℕ, b ^ (2 ^ k) = 1

variable [Finite V]

theorem exists_altBlock (hV : ∀ v : V, v ^ 2 = 1) {B : Subgroup (MulAut V)} (hperf : ⁅B, B⁆ = B)
    (hshort : IsShortGroup ↥(yuHol B)) {n : ℕ} (hn : 2 ≤ n)
    (hnat : IsNaturalAltModule ↥(yuHol B) n) : Nonempty (AltBlock B n) := by
  classical
  have hperf' : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.mpr hperf
  obtain ⟨D⟩ := SolK.exists_altBlockData hshort hn hnat
  obtain ⟨φ, -⟩ := hnat
  have hU : shortU ↥(yuHol B) = (yuInc B).range := shortU_eq_range B φ hV hshort
  let ι : ↥(commV B) →* ↥(shortU ↥(yuHol B)) :=
    (yuInc B).codRestrict (shortU ↥(yuHol B)) (yuInc_mem_shortU B hV)
  have hιinj : Function.Injective ι := fun a b h =>
    yuInc_injective B (congrArg Subtype.val h)
  have hιsurj : Function.Surjective ι := by
    rintro ⟨x, hx⟩
    obtain ⟨u, hu⟩ : x ∈ (yuInc B).range := hU ▸ hx
    exact ⟨u, Subtype.ext hu⟩
  let eι : ↥(commV B) ≃* ↥(shortU ↥(yuHol B)) := MulEquiv.ofBijective ι ⟨hιinj, hιsurj⟩
  have hker : ∀ b : ↥B, D.ρ (yuSec B b) = 1 → yuSec B b ∈ pCore 2 ↥(yuHol B) := fun b hb => by
    rw [← D.ker_ρ]; exact hb
  refine ⟨{ θ := D.ρ.comp (yuSec B)
            θ_alt := fun b => D.ρ_alt _
            θ_surj := ?_
            β := eι.trans D.β
            equivar := ?_
            ker_central := ?_
            ker_two := ?_ }⟩
  · intro a ha
    obtain ⟨l, hl⟩ := D.ρ_surj a ha
    refine ⟨yuProj B l, ?_⟩
    have h1 := yu_eq_inc_mul_sec B l
    have h2 : D.ρ (yuInc B ⟨l.1.left, l.2.1⟩) = 1 := by
      have hmem := yuInc_range_le_pCore B hV ⟨⟨l.1.left, l.2.1⟩, rfl⟩
      rw [← D.ker_ρ] at hmem
      exact hmem
    show D.ρ (yuSec B (yuProj B l)) = a
    rw [← hl]
    conv_rhs => rw [h1]
    rw [map_mul, h2, one_mul]
    rfl
  · intro b e
    have hu : (yuSec B b) * ((ι e : ↥(shortU ↥(yuHol B))) : ↥(yuHol B)) * (yuSec B b)⁻¹ ∈
        shortU ↥(yuHol B) :=
      (shortU_normal (L := ↥(yuHol B))).conj_mem _ (ι e).2 _
    have h1 := D.equivar (yuSec B b) (ι e) hu
    have h2 : (⟨(yuSec B b) * ((ι e : ↥(shortU ↥(yuHol B))) : ↥(yuHol B)) * (yuSec B b)⁻¹, hu⟩ :
        ↥(shortU ↥(yuHol B))) = ι ⟨(b : MulAut V) (e : V), apply_mem_commV_self B b.2 e.2⟩ :=
      Subtype.ext (conj_yuInc B (yuSec B b) e)
    rw [h2] at h1
    exact h1
  · intro b hb
    have hrp := hker b hb
    have := yuTheta_ker_le_center B φ hV hshort
    exact this ((yuTheta_eq_one_iff B φ b).mpr hrp)
  · intro b hb
    have hrp := hker b hb
    have h2 : IsPGroup 2 ↥(pCore 2 ↥(yuHol B)) := pCore_isPGroup
    obtain ⟨k, hk⟩ := h2 ⟨yuSec B b, hrp⟩
    refine ⟨k, yuSec_injective B ?_⟩
    have := congrArg Subtype.val hk
    simpa [map_pow] using this

end Data

section Lemmas

variable {V : Type} [CommGroup V] [Finite V] {B : Subgroup (MulAut V)} {n : ℕ}

omit [Finite V] in
theorem AltBlock.card_commV (D : AltBlock B n) : Nat.card ↥(commV B) = 2 ^ (2 * n) := by
  have h1 := Nat.card_congr D.β.toEquiv
  have h2 := card_coreMod_mul_two (odd_two_mul_add_one n)
  rw [h1]
  have h3 : 2 ^ (2 * n + 1) = 2 ^ (2 * n) * 2 := pow_succ 2 (2 * n)
  rw [h3] at h2
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2

omit [Finite V] in
theorem mem_commV_of_normalizer {x : MulAut V} (hx : x ∈ Subgroup.normalizer (B : Set (MulAut V)))
    {e : V} (he : e ∈ commV B) : x e ∈ commV B :=
  apply_mem_of_mem_stabV (mem_stabV_commV hx) he

omit [Finite V] in
theorem AltBlock.exists_perm (D : AltBlock B n) (hn : 2 ≤ n) {x : MulAut V}
    (hx : x ∈ Subgroup.normalizer (B : Set (MulAut V))) :
    ∃ π : Equiv.Perm (Fin (2 * n + 1)), ∀ (e : ↥(commV B)) (he : x (e : V) ∈ commV B),
      D.β ⟨x (e : V), he⟩ = coreAct (2 * n + 1) π (D.β e) := by
  have hodd : Odd (2 * n + 1) := odd_two_mul_add_one n
  have h5 : 5 ≤ 2 * n + 1 := by omega
  have hxs : x ∈ stabV (commV B) := mem_stabV_commV hx
  let xE : ↥(commV B) ≃* ↥(commV B) := resStab (commV B) ⟨x, hxs⟩
  have hxE : ∀ e : ↥(commV B), ((xE e : ↥(commV B)) : V) = x (e : V) := fun e => rfl
  let γ : MulAut ↥(coreMod (2 * n + 1)) := (D.β.symm.trans xE).trans D.β
  have hγ : ∀ e : ↥(commV B), γ (D.β e) = D.β (xE e) := fun e => by
    show D.β (xE (D.β.symm (D.β e))) = _
    rw [MulEquiv.symm_apply_apply]
  have key : ∀ (b b' : ↥B), (b' : MulAut V) * x = x * (b : MulAut V) → ∀ e : ↥(commV B),
      γ (coreAct (2 * n + 1) (D.θ b) (D.β e)) = coreAct (2 * n + 1) (D.θ b') (γ (D.β e)) := by
    intro b b' hbb e
    rw [← D.equivar b e, hγ, hγ, ← D.equivar b' (xE e)]
    congr 1
    apply Subtype.ext
    show x ((b : MulAut V) (e : V)) = (b' : MulAut V) (x (e : V))
    have := congrArg (fun f : MulAut V => f (e : V)) hbb
    simpa [MulAut.mul_apply] using this.symm
  have hy : ∀ σ ∈ alternatingGroup (Fin (2 * n + 1)), ∃ σ' ∈ alternatingGroup (Fin (2 * n + 1)),
      ∀ d, γ (coreAct (2 * n + 1) σ d) = coreAct (2 * n + 1) σ' (γ d) := by
    intro σ hσ
    obtain ⟨b, rfl⟩ := D.θ_surj σ hσ
    have hb' : x * (b : MulAut V) * x⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hx _).mp b.2
    refine ⟨D.θ ⟨_, hb'⟩, D.θ_alt _, fun d => ?_⟩
    obtain ⟨e, rfl⟩ := D.β.surjective d
    refine key b ⟨_, hb'⟩ ?_ e
    show x * (b : MulAut V) * x⁻¹ * x = x * (b : MulAut V)
    group
  have hy' : ∀ σ' ∈ alternatingGroup (Fin (2 * n + 1)), ∃ σ ∈ alternatingGroup (Fin (2 * n + 1)),
      ∀ d, γ (coreAct (2 * n + 1) σ d) = coreAct (2 * n + 1) σ' (γ d) := by
    intro σ' hσ'
    obtain ⟨b', rfl⟩ := D.θ_surj σ' hσ'
    have hb : x⁻¹ * (b' : MulAut V) * x ∈ B := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hx) _).mp b'.2
      simpa using this
    refine ⟨D.θ ⟨_, hb⟩, D.θ_alt _, fun d => ?_⟩
    obtain ⟨e, rfl⟩ := D.β.surjective d
    refine key ⟨_, hb⟩ b' ?_ e
    show (b' : MulAut V) * x = x * (x⁻¹ * (b' : MulAut V) * x)
    group
  obtain ⟨π, hπ⟩ := exists_perm_of_normalizes_alt hodd h5 γ hy hy'
  refine ⟨π, fun e he => ?_⟩
  have h1 : (⟨x (e : V), he⟩ : ↥(commV B)) = xE e := Subtype.ext rfl
  rw [h1, ← hγ, hπ]

omit [Finite V] in
theorem AltBlock.eq_one_of_trivial (D : AltBlock B n) (hn : 2 ≤ n) {b : ↥B}
    (h : ∀ e : ↥(commV B), (b : MulAut V) (e : V) = (e : V)) : D.θ b = 1 := by
  have h3 : 3 ≤ 2 * n + 1 := by omega
  apply coreAct_injective h3
  rw [map_one]
  ext d
  obtain ⟨e, rfl⟩ := D.β.surjective d
  rw [← D.equivar b e]
  have : (⟨(b : MulAut V) (e : V), apply_mem_commV_self B b.2 e.2⟩ : ↥(commV B)) = e :=
    Subtype.ext (h e)
  rw [this]
  rfl

omit [Finite V] in
theorem AltBlock.centralizes_of_trivial (D : AltBlock B n) (hn : 2 ≤ n)
    (hR : ∀ b : ↥B, D.θ b = 1 → b = 1) {x : MulAut V}
    (hx : x ∈ Subgroup.normalizer (B : Set (MulAut V)))
    (hxE : ∀ e ∈ commV B, x e = e) : ∀ b ∈ B, b * x = x * b := by
  intro b hb
  have hc : x * b * x⁻¹ * b⁻¹ ∈ B := by
    have h1 : x * b * x⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hx b).mp hb
    exact B.mul_mem h1 (B.inv_mem hb)
  have hxinv : ∀ e ∈ commV B, x⁻¹ e = e := by
    intro e he
    have := hxE e he
    calc x⁻¹ e = x⁻¹ (x e) := by rw [this]
      _ = e := MulAut.inv_apply_self _ _ _
  have htriv : ∀ e : ↥(commV B), (x * b * x⁻¹ * b⁻¹ : MulAut V) (e : V) = (e : V) := by
    intro e
    have h1 : b⁻¹ (e : V) ∈ commV B := apply_mem_commV_self B (B.inv_mem hb) e.2
    have h2 : (x⁻¹ * b⁻¹ : MulAut V) (e : V) = b⁻¹ (e : V) := by
      rw [MulAut.mul_apply, hxinv _ h1]
    calc (x * b * x⁻¹ * b⁻¹ : MulAut V) (e : V) = x (b ((x⁻¹ * b⁻¹ : MulAut V) (e : V))) := by
          simp [MulAut.mul_apply]
      _ = x (b (b⁻¹ (e : V))) := by rw [h2]
      _ = x (e : V) := by rw [MulAut.apply_inv_self]
      _ = (e : V) := hxE _ e.2
  have h1 : D.θ ⟨x * b * x⁻¹ * b⁻¹, hc⟩ = 1 := D.eq_one_of_trivial hn htriv
  have h2 := hR _ h1
  have h3 : x * b * x⁻¹ * b⁻¹ = 1 := congrArg Subtype.val h2
  calc b * x = (x * b * x⁻¹ * b⁻¹)⁻¹ * (x * b) := by group
    _ = x * b := by rw [h3]; group

omit [Finite V] in
theorem odd_orderOf_of_pow_three {x : MulAut V} (hx3 : x ^ 3 = 1) : Odd (orderOf x) :=
  Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hx3)

theorem AltBlock.card_comm_perm (D : AltBlock B n) (hV : ∀ v : V, v ^ 2 = 1) {x : MulAut V}
    (hxB : x ∈ B) (hx3 : x ^ 3 = 1) :
    Nat.card ↥(commV (Subgroup.zpowers (coreAct (2 * n + 1) (D.θ ⟨x, hxB⟩)))) =
      Nat.card ↥(commV (Subgroup.zpowers x)) := by
  set g : MulAut ↥(coreMod (2 * n + 1)) := coreAct (2 * n + 1) (D.θ ⟨x, hxB⟩) with hg
  have hU : commV (Subgroup.zpowers x) ≤ commV B :=
    commV_mono (Subgroup.zpowers_le.mpr hxB)
  have hUmap : commV (Subgroup.zpowers x) = (⊤ : Subgroup V).map (commHom x) :=
    commV_zpowers_eq_map x
  have hdec := (S153E55.decomp_top hV (odd_orderOf_of_pow_three hx3)).1
  have hcomp : ∀ v : V, ∃ w ∈ commV (Subgroup.zpowers x), commHom x v = commHom x w := by
    intro v
    have hv : v ∈ fixV (Subgroup.zpowers x) ⊔ commV (Subgroup.zpowers x) := by
      rw [hdec]; exact Subgroup.mem_top v
    obtain ⟨c, hc, w, hw, rfl⟩ := Subgroup.mem_sup.mp hv
    refine ⟨w, hw, ?_⟩
    have hc1 : commHom x c = 1 := by
      have : c ∈ (commHom x).ker := by rw [ker_commHom]; exact hc
      exact this
    rw [map_mul, hc1, one_mul]
  have hβ : ∀ (e : ↥(commV B)) (h : commHom x (e : V) ∈ commV B),
      D.β ⟨commHom x (e : V), h⟩ = commHom g (D.β e) := by
    intro e h
    have h1 := D.equivar ⟨x, hxB⟩ e
    have h2 : (⟨commHom x (e : V), h⟩ : ↥(commV B)) =
        ⟨x (e : V), apply_mem_commV_self B hxB e.2⟩ * e⁻¹ := Subtype.ext rfl
    rw [h2, map_mul, map_inv, h1]
    rfl
  set Ũ : Subgroup ↥(commV B) := (commV (Subgroup.zpowers x)).subgroupOf (commV B) with hŨ
  have hcardŨ : Nat.card ↥Ũ = Nat.card ↥(commV (Subgroup.zpowers x)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU).toEquiv
  have hmap : Ũ.map D.β.toMonoidHom = commV (Subgroup.zpowers g) := by
    rw [commV_zpowers_eq_map g]
    ext w
    constructor
    · rintro ⟨e, he, rfl⟩
      have heU : (e : V) ∈ commV (Subgroup.zpowers x) := he
      rw [hUmap] at heU
      obtain ⟨v, -, hv⟩ := Subgroup.mem_map.mp heU
      obtain ⟨w', hw'U, hw'⟩ := hcomp v
      refine Subgroup.mem_map.mpr ⟨D.β ⟨w', hU hw'U⟩, Subgroup.mem_top _, ?_⟩
      rw [← hβ ⟨w', hU hw'U⟩ (by
        have : commHom x w' = (e : V) := by rw [← hw', hv]
        rw [this]; exact e.2)]
      show D.β ⟨commHom x w', _⟩ = D.β e
      congr 1
      apply Subtype.ext
      show commHom x w' = (e : V)
      rw [← hw', hv]
    · intro hw
      obtain ⟨δ, -, rfl⟩ := Subgroup.mem_map.mp hw
      obtain ⟨e, rfl⟩ := D.β.surjective δ
      have hmemB : commHom x (e : V) ∈ commV B := by
        have h1 := apply_mem_commV_self B hxB e.2
        rw [commHom_apply]
        exact mul_mem h1 (inv_mem e.2)
      refine ⟨⟨commHom x (e : V), hmemB⟩, ?_, ?_⟩
      · show commHom x (e : V) ∈ commV (Subgroup.zpowers x)
        rw [hUmap]
        exact Subgroup.mem_map.mpr ⟨(e : V), Subgroup.mem_top _, rfl⟩
      · exact hβ e hmemB
  rw [← hmap]
  exact (Subgroup.card_map_of_injective D.β.injective).trans hcardŨ

theorem AltBlock.isThreeCycle_of_mem (D : AltBlock B n) (hV : ∀ v : V, v ^ 2 = 1) {x : MulAut V}
    (hxB : x ∈ B) (hx3 : x ^ 3 = 1) (hc : Nat.card ↥(commV (Subgroup.zpowers x)) = 4) :
    (D.θ ⟨x, hxB⟩).IsThreeCycle := by
  have hd3 : (D.θ ⟨x, hxB⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxB⟩ : ↥B) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  refine sym_isThreeCycle (2 * n + 1) (odd_two_mul_add_one n) hd3 ?_
  have hmap : (Subgroup.zpowers (D.θ ⟨x, hxB⟩)).map (coreAct (2 * n + 1)) =
      Subgroup.zpowers (coreAct (2 * n + 1) (D.θ ⟨x, hxB⟩)) := MonoidHom.map_zpowers _ _
  exact (congrArg (fun S => Nat.card ↥(commV S)) hmap).trans
    ((D.card_comm_perm hV hxB hx3).trans hc)

theorem AltBlock.normalizer_dichotomy (D : AltBlock B n) (hV : ∀ v : V, v ^ 2 = 1)
    (hn : 2 ≤ n) (hR : ∀ b : ↥B, D.θ b = 1 → b = 1) {x : MulAut V}
    (hx : x ∈ Subgroup.normalizer (B : Set (MulAut V))) (hx3 : x ^ 3 = 1)
    (hc : Nat.card ↥(commV (Subgroup.zpowers x)) = 4) :
    (∀ b ∈ B, b * x = x * b) ∨ x ∈ B := by
  have h3 : 3 ≤ 2 * n + 1 := by omega
  obtain ⟨π, hπ⟩ := D.exists_perm hn hx
  have hxE : ∀ e : ↥(commV B), x (e : V) ∈ commV B := fun e => mem_commV_of_normalizer hx e.2
  have hπ' : ∀ e : ↥(commV B), D.β ⟨x (e : V), hxE e⟩ = coreAct (2 * n + 1) π (D.β e) :=
    fun e => hπ e (hxE e)
  by_cases hπ1 : π = 1
  · left
    refine D.centralizes_of_trivial hn hR hx (fun e he => ?_)
    have h1 := hπ' ⟨e, he⟩
    rw [hπ1, map_one] at h1
    have h2 : (⟨x e, hxE ⟨e, he⟩⟩ : ↥(commV B)) = ⟨e, he⟩ := D.β.injective (by rw [h1]; rfl)
    exact congrArg Subtype.val h2
  · right
    have hπ3 : π ^ 3 = 1 := by
      apply coreAct_injective h3
      rw [map_pow, map_one]
      refine MulEquiv.ext fun d => ?_
      obtain ⟨e, rfl⟩ := D.β.surjective d
      have e1 := hπ' e
      have e2 := hπ' ⟨x (e : V), hxE e⟩
      have e3 := hπ' ⟨x (x (e : V)), hxE ⟨x (e : V), hxE e⟩⟩
      have hxxx : x (x (x (e : V))) = (e : V) := by
        have : (x ^ 3) (e : V) = (e : V) := by rw [hx3]; rfl
        simpa [pow_succ, MulAut.mul_apply] using this
      have e4 : (⟨x (x (x (e : V))), hxE ⟨x (x (e : V)), hxE ⟨x (e : V), hxE e⟩⟩⟩ :
          ↥(commV B)) = e := Subtype.ext hxxx
      have : D.β e = coreAct (2 * n + 1) π (coreAct (2 * n + 1) π (coreAct (2 * n + 1) π
          (D.β e))) := by
        rw [← e1, ← e2, ← e3, e4]
      show (coreAct (2 * n + 1) π ^ 3) (D.β e) = D.β e
      simpa [pow_succ, MulAut.mul_apply] using this.symm
    have hπalt : π ∈ alternatingGroup (Fin (2 * n + 1)) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      have h1 : Equiv.Perm.sign π ^ 3 = 1 := by rw [← map_pow, hπ3, map_one]
      have h2 : Equiv.Perm.sign π ^ 2 = 1 := Int.units_sq _
      calc Equiv.Perm.sign π = Equiv.Perm.sign π ^ 3 * (Equiv.Perm.sign π ^ 2)⁻¹ := by group
        _ = 1 := by rw [h1, h2]; simp
    obtain ⟨b, hb⟩ := D.θ_surj π hπalt
    have hUE : commV (Subgroup.zpowers x) ≤ commV B := by
      set U := commV (Subgroup.zpowers x) with hU
      set P : Subgroup V := (commV B).map (commHom x) with hP
      have hPU : P ≤ U := by
        rw [hU, commV_zpowers_eq_map x]
        exact Subgroup.map_mono le_top
      have hPE : P ≤ commV B := by
        rintro _ ⟨e, he, rfl⟩
        rw [commHom_apply]
        exact mul_mem (hxE ⟨e, he⟩) (inv_mem he)
      have hdec := (S153E55.decomp_top hV (odd_orderOf_of_pow_three hx3)).2
      have hP' : P = ⊥ ∨ P = U := by
        refine CGT6E.klein_inv hc hPU hx3 ?_ ?_
        · rintro _ ⟨e, he, rfl⟩
          refine ⟨x e, hxE ⟨e, he⟩, ?_⟩
          simp [commHom_apply, map_mul, map_inv]
        · intro u hu hxu
          have : u ∈ fixV (Subgroup.zpowers x) ⊓ commV (Subgroup.zpowers x) :=
            ⟨mem_fixV_zpowers_iff.mpr hxu, hu⟩
          rw [hdec] at this
          exact (Subgroup.mem_bot.mp this)
      rcases hP' with h | h
      · exfalso
        apply hπ1
        apply coreAct_injective h3
        rw [map_one]
        refine MulEquiv.ext fun d => ?_
        obtain ⟨e, rfl⟩ := D.β.surjective d
        have h1 : commHom x (e : V) ∈ P := ⟨(e : V), e.2, rfl⟩
        rw [h, Subgroup.mem_bot, commHom_apply, mul_inv_eq_one] at h1
        have h2 : (⟨x (e : V), hxE e⟩ : ↥(commV B)) = e := Subtype.ext h1
        rw [← hπ' e, h2]
        rfl
      · rw [← h]; exact hPE
    set a : MulAut V := (b : MulAut V) with ha
    have haB : a ∈ B := b.2
    have haN : a ∈ Subgroup.normalizer (B : Set (MulAut V)) := Subgroup.le_normalizer haB
    set c : MulAut V := a⁻¹ * x with hcdef
    have hcN : c ∈ Subgroup.normalizer (B : Set (MulAut V)) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ haN) hx
    have hcE : ∀ e ∈ commV B, c e = e := by
      intro e he
      have h1 := D.equivar b⁻¹ ⟨x e, hxE ⟨e, he⟩⟩
      have h2 : D.θ b⁻¹ = π⁻¹ := by rw [map_inv, hb]
      have h3' : ((b⁻¹ : ↥B) : MulAut V) = a⁻¹ := rfl
      have h4 : (⟨((b⁻¹ : ↥B) : MulAut V) (x e), apply_mem_commV_self B (b⁻¹).2 (hxE ⟨e, he⟩)⟩ :
          ↥(commV B)) = ⟨c e, by
            have := apply_mem_commV_self B (b⁻¹).2 (hxE ⟨e, he⟩)
            exact this⟩ := Subtype.ext rfl
      have h5 : D.β ⟨c e, apply_mem_commV_self B (b⁻¹).2 (hxE ⟨e, he⟩)⟩ = D.β ⟨e, he⟩ := by
        rw [← h4, h1, h2, hπ' ⟨e, he⟩]
        simp
      exact congrArg Subtype.val (D.β.injective h5)
    have hcomm : ∀ b' ∈ B, b' * c = c * b' :=
      D.centralizes_of_trivial hn hR hcN hcE
    have hcV : ∀ v : V, c v * v⁻¹ ∈ commV B := by
      intro v
      have e1 : c v * v⁻¹ = a⁻¹ (x v * v⁻¹) * (a⁻¹ v * v⁻¹) := by
        simp [hcdef, MulAut.mul_apply, map_mul, map_inv, mul_assoc, mul_comm, mul_left_comm]
      rw [e1]
      refine mul_mem ?_ (G6.mem_commV_of_mem (Subgroup.inv_mem _ haB) v)
      have h1 : x v * v⁻¹ ∈ commV (Subgroup.zpowers x) :=
        G6.mem_commV_of_mem (Subgroup.mem_zpowers x) v
      exact apply_mem_commV_self B (Subgroup.inv_mem _ haB) (hUE h1)
    have hc2 : c ^ 2 = 1 := by
      refine MulEquiv.ext fun v => ?_
      obtain ⟨w, hw⟩ : ∃ w : V, w = c v * v⁻¹ := ⟨_, rfl⟩
      have hwE : w ∈ commV B := hw ▸ hcV v
      have hcw : c w = w := hcE w hwE
      have hw2 : w ^ 2 = 1 := hV w
      have hwv : c v = w * v := by rw [hw]; exact (inv_mul_cancel_right (c v) v).symm
      show c (c v) = v
      rw [hwv, map_mul, hcw, hwv, ← mul_assoc, ← pow_two w, hw2, one_mul]
    have ha3 : a ^ 3 = 1 := by
      have h1 : D.θ (b ^ 3) = 1 := by rw [map_pow, hb, hπ3]
      have := hR _ h1
      exact congrArg Subtype.val this
    have hac : Commute a c := hcomm a haB
    have hxac : x = a * c := by simp [hcdef]
    have hc3 : c ^ 3 = 1 := by
      have h1 : x ^ 3 = a ^ 3 * c ^ 3 := by
        rw [hxac]; exact hac.mul_pow 3
      rw [hx3, ha3, one_mul] at h1
      exact h1.symm
    have hc1 : c = 1 := by
      calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
        _ = 1 := by rw [hc3, hc2]; simp
    rw [hxac, hc1, mul_one]
    exact haB

end Lemmas

end CFSG.CGT.PushingUpLit.CGT6
