module

public import CFSG.CGT.PushingUpLit.BHS6.SymLocalGrp
public import CFSG.CGT.PushingUpLit.BHS6.SixEightType
public import CFSG.CGT.PushingUpLit.BHS6.SymOffenderBasic

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {n : ℕ}

structure SymNatData (G V : Subgroup Γ) (n : ℕ) (φ : ↥G →* Equiv.Perm (Fin n))
    (ψ : ↥V →* ↥(coreMod n)) : Prop where
  normal : G ≤ Subgroup.normalizer (V : Set Γ)
  elemAbelian : IsElemAbelian 2 V
  φ_surj : Function.Surjective φ
  φ_ker : φ.ker = (G ⊓ Subgroup.centralizer (V : Set Γ)).subgroupOf G
  ψ_surj : Function.Surjective ψ
  ψ_ker : ψ.ker = (V ⊓ Subgroup.centralizer (G : Set Γ)).subgroupOf V
  equivar : ∀ (e : ↥G) (v : ↥V) (hv : (e : Γ) * v * (e : Γ)⁻¹ ∈ V),
    ψ ⟨(e : Γ) * v * (e : Γ)⁻¹, hv⟩ = coreAct n (φ e) (ψ v)

variable {G V : Subgroup Γ} {φ : ↥G →* Equiv.Perm (Fin n)} {ψ : ↥V →* ↥(coreMod n)}

namespace SymNatData

theorem conj_mem (D : SymNatData G V n φ ψ) {g : Γ} (hg : g ∈ G) {v : Γ} (hv : v ∈ V) :
    g * v * g⁻¹ ∈ V :=
  (Subgroup.mem_normalizer_iff.mp (D.normal hg) v).mp hv

theorem centralizes_of_map_eq_one (D : SymNatData G V n φ ψ) {g : Γ} (hg : g ∈ G)
    (h : φ ⟨g, hg⟩ = 1) {v : Γ} (hv : v ∈ V) : g * v = v * g := by
  have h1 : (⟨g, hg⟩ : ↥G) ∈ φ.ker := h
  rw [D.φ_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h1
  have := Subgroup.mem_centralizer_iff.mp h1.2 v hv
  exact this.symm

theorem conj_eq_of_map_eq_one (D : SymNatData G V n φ ψ) {g : Γ} (hg : g ∈ G)
    (h : φ ⟨g, hg⟩ = 1) {v : Γ} (hv : v ∈ V) : g * v * g⁻¹ = v := by
  rw [D.centralizes_of_map_eq_one hg h hv]
  group

theorem centralizes_of_ψ_eq_one (D : SymNatData G V n φ ψ) {v : ↥V} (h : ψ v = 1) {g : Γ}
    (hg : g ∈ G) : g * v = v * g := by
  have h1 : v ∈ ψ.ker := h
  rw [D.ψ_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h1
  exact Subgroup.mem_centralizer_iff.mp h1.2 g hg

end SymNatData

structure LocalPts (p : Fin 3 → Fin n) (Y : Subgroup (Equiv.Perm (Fin n))) : Prop where
  inj : Function.Injective p
  le_stab : Y ≤ setStab (triSet p)
  d_mem : triCyc p ∈ Y
  normalizes : Y ≤ Subgroup.normalizer (Subgroup.zpowers (triCyc p) : Set (Equiv.Perm (Fin n)))
  swap_mem : Equiv.swap (p 0) (p 2) ∈ Y

@[expose] def suppV (V : Subgroup Γ) (ψ : ↥V →* ↥(coreMod n)) (A : Finset (Fin n)) : Subgroup Γ :=
  ((suppSub A).comap ψ).map V.subtype

theorem mem_suppV {ψ : ↥V →* ↥(coreMod n)} {A : Finset (Fin n)} {x : Γ} :
    x ∈ suppV V ψ A ↔ ∃ hx : x ∈ V, ψ ⟨x, hx⟩ ∈ suppSub A := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

section Local

variable (D : SymNatData G V n φ ψ) {p : Fin 3 → Fin n} {Y : Subgroup (Equiv.Perm (Fin n))}

@[expose] def nGrp (G : Subgroup Γ) (φ : ↥G →* Equiv.Perm (Fin n)) (p : Fin 3 → Fin n) :
    Subgroup Γ := preimG G φ (Subgroup.zpowers (triCyc p))

@[expose] def uMod (G V : Subgroup Γ) (φ : ↥G →* Equiv.Perm (Fin n)) (p : Fin 3 → Fin n) :
    Subgroup Γ := ⁅nGrp G φ p, V⁆

include D in
theorem uMod_le_V : uMod G V φ p ≤ V := by
  rw [uMod, Subgroup.commutator_le]
  intro n hn v hv
  have hnG : n ∈ G := preimG_le G φ _ hn
  have h1 : n * v * n⁻¹ ∈ V := D.conj_mem hnG hv
  have h2 := V.mul_mem h1 (V.inv_mem hv)
  simpa [commutatorElement_def, mul_assoc] using h2

include D in
theorem ψ_commutator {n' : Γ} (hnG : n' ∈ G) {v : ↥V} (hc : ⁅n', (v : Γ)⁆ ∈ V) :
    ψ ⟨⁅n', (v : Γ)⁆, hc⟩ = coreAct n (φ ⟨n', hnG⟩) (ψ v) * (ψ v)⁻¹ := by
  have h1 : n' * (v : Γ) * n'⁻¹ ∈ V := D.conj_mem hnG v.2
  have e : (⟨⁅n', (v : Γ)⁆, hc⟩ : ↥V) = ⟨n' * (v : Γ) * n'⁻¹, h1⟩ * v⁻¹ := by
    apply Subtype.ext
    simp [commutatorElement_def, mul_assoc]
  rw [e, map_mul, map_inv, D.equivar ⟨n', hnG⟩ v h1]
  rfl

theorem zpowers_fix {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ Subgroup.zpowers (triCyc p)) {j : Fin n}
    (hj : j ∉ triSet p) : σ j = j := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hσ
  exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (triCyc_apply_of_notMem hj) k

include D in
theorem uMod_le_suppV : uMod G V φ p ≤ suppV V ψ (triSet p) := by
  rw [uMod, Subgroup.commutator_le]
  intro n hn v hv
  have hnG : n ∈ G := preimG_le G φ _ hn
  have hnd : φ ⟨n, hnG⟩ ∈ Subgroup.zpowers (triCyc p) := (mem_preimG.1 hn).2
  have hc : ⁅n, v⁆ ∈ V := by
    have h1 : n * v * n⁻¹ ∈ V := D.conj_mem hnG hv
    have h2 := V.mul_mem h1 (V.inv_mem hv)
    simpa [commutatorElement_def, mul_assoc] using h2
  refine mem_suppV.2 ⟨hc, ?_⟩
  have := ψ_commutator D hnG (v := ⟨v, hv⟩) hc
  rw [this]
  exact coreAct_mul_inv_mem_suppSub (fun j hj => zpowers_fix hnd hj) _

@[expose] def normEnd {M : Type*} [CommGroup M] (α : MulAut M) : M →* M :=
  MonoidHom.mk' (fun x => x * α x * α (α x)) fun x y => by
    simp only [map_mul]
    ac_rfl

theorem normEnd_apply_apply {M : Type*} [CommGroup M] {α : MulAut M} (h3 : ∀ x, α (α (α x)) = x)
    (x : M) : normEnd α (α x) = normEnd α x := by
  simp only [normEnd, MonoidHom.mk'_apply, h3]
  ac_rfl

theorem normEnd_zpow {M : Type*} [CommGroup M] {α : MulAut M} (h3 : ∀ x, α (α (α x)) = x)
    (j : ℤ) (x : M) : normEnd α ((α ^ j) x) = normEnd α x := by
  let S : Subgroup (MulAut M) :=
    { carrier := {a | ∀ w, normEnd α (a w) = normEnd α w}
      one_mem' := fun w => rfl
      mul_mem' := fun {a b} ha hb w => by
        rw [MulAut.mul_apply, ha, hb]
      inv_mem' := fun {a} ha w => by
        have := ha (a⁻¹ w)
        rw [MulAut.apply_inv_self] at this
        exact this.symm }
  have hα : α ∈ S := fun w => normEnd_apply_apply h3 w
  exact S.zpow_mem hα j x

include D in
theorem eq_one_of_mem_uMod (hp : LocalPts p Y) {u : ↥V} (hu : (u : Γ) ∈ uMod G V φ p)
    (h : ψ u = 1) : u = 1 := by
  classical
  have hVe := D.elemAbelian
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  obtain ⟨n₀, hn₀⟩ := D.φ_surj (triCyc p)
  set α : MulAut ↥V := conjAct V ⟨(n₀ : Γ), D.normal n₀.2⟩ with hα
  have hαcoe : ∀ x : ↥V, ((α x : ↥V) : Γ) = (n₀ : Γ) * x * (n₀ : Γ)⁻¹ := fun x =>
    conjAct_apply' V ⟨(n₀ : Γ), D.normal n₀.2⟩ x
  have hα3 : ∀ x : ↥V, α (α (α x)) = x := by
    intro x
    apply Subtype.ext
    rw [hαcoe, hαcoe, hαcoe]
    have hφ3 : φ ⟨(n₀ : Γ) ^ 3, G.pow_mem n₀.2 3⟩ = 1 := by
      have : (⟨(n₀ : Γ) ^ 3, G.pow_mem n₀.2 3⟩ : ↥G) = n₀ ^ 3 := rfl
      rw [this, map_pow, hn₀]
      exact triCyc_pow_three hp.inj
    have := D.conj_eq_of_map_eq_one (G.pow_mem n₀.2 3) hφ3 x.2
    calc (n₀ : Γ) * ((n₀ : Γ) * ((n₀ : Γ) * (x : Γ) * (n₀ : Γ)⁻¹) * (n₀ : Γ)⁻¹) * (n₀ : Γ)⁻¹
        = (n₀ : Γ) ^ 3 * x * ((n₀ : Γ) ^ 3)⁻¹ := by
          simp only [pow_succ, pow_zero, one_mul]
          group
      _ = x := this
  have hαzpow : ∀ (j : ℤ) (x : ↥V),
      (((α ^ j) x : ↥V) : Γ) = (n₀ : Γ) ^ j * x * ((n₀ : Γ) ^ j)⁻¹ := by
    intro j x
    have e : α ^ j = conjAct V ((⟨(n₀ : Γ), D.normal n₀.2⟩ :
        ↥(Subgroup.normalizer (V : Set Γ))) ^ j) := (map_zpow (conjAct V) _ j).symm
    rw [e, conjAct_apply']
    simp
  let Xk : Subgroup Γ := (normEnd α).ker.map V.subtype
  have hUX : uMod G V φ p ≤ Xk := by
    rw [uMod, Subgroup.commutator_le]
    intro n' hn v hv
    have hnG : n' ∈ G := preimG_le G φ _ hn
    have hnd : φ ⟨n', hnG⟩ ∈ Subgroup.zpowers (triCyc p) := (mem_preimG.1 hn).2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hnd
    have hc : ⁅n', v⁆ ∈ V := by
      have h1 : n' * v * n'⁻¹ ∈ V := D.conj_mem hnG hv
      have h2 := V.mul_mem h1 (V.inv_mem hv)
      simpa [commutatorElement_def, mul_assoc] using h2
    refine ⟨⟨⁅n', v⁆, hc⟩, ?_, rfl⟩
    have hkG : n' * ((n₀ : Γ) ^ j)⁻¹ ∈ G := G.mul_mem hnG (G.inv_mem (G.zpow_mem n₀.2 j))
    have hkφ : φ ⟨n' * ((n₀ : Γ) ^ j)⁻¹, hkG⟩ = 1 := by
      have e : (⟨n' * ((n₀ : Γ) ^ j)⁻¹, hkG⟩ : ↥G) = ⟨n', hnG⟩ * (n₀ ^ j)⁻¹ := rfl
      rw [e, map_mul, map_inv, map_zpow, hn₀, hj]
      simp
    have hact : n' * v * n'⁻¹ = (n₀ : Γ) ^ j * v * ((n₀ : Γ) ^ j)⁻¹ := by
      have hw : (n₀ : Γ) ^ j * v * ((n₀ : Γ) ^ j)⁻¹ ∈ V :=
        D.conj_mem (G.zpow_mem n₀.2 j) hv
      have h1 := D.conj_eq_of_map_eq_one hkG hkφ hw
      have e : n' * v * n'⁻¹ = (n' * ((n₀ : Γ) ^ j)⁻¹) * ((n₀ : Γ) ^ j * v * ((n₀ : Γ) ^ j)⁻¹) *
          (n' * ((n₀ : Γ) ^ j)⁻¹)⁻¹ := by group
      rw [e, h1]
    have hgen : (⟨⁅n', v⁆, hc⟩ : ↥V) = (α ^ j) ⟨v, hv⟩ * (⟨v, hv⟩ : ↥V)⁻¹ := by
      apply Subtype.ext
      rw [show (((α ^ j) ⟨v, hv⟩ * (⟨v, hv⟩ : ↥V)⁻¹ : ↥V) : Γ) =
        (((α ^ j) ⟨v, hv⟩ : ↥V) : Γ) * v⁻¹ from rfl, hαzpow, ← hact]
      simp [commutatorElement_def, mul_assoc]
    have hker : normEnd α ⟨⁅n', v⁆, hc⟩ = 1 := by
      rw [hgen, map_mul, map_inv, normEnd_zpow hα3]
      exact mul_inv_cancel _
    exact hker
  have hux : (u : Γ) ∈ Xk := hUX hu
  obtain ⟨u', hu', hu'e⟩ := hux
  have hu'u : u' = u := Subtype.ext hu'e
  rw [hu'u] at hu'
  have hnorm : normEnd α u = 1 := hu'
  have hfix : α u = u := by
    apply Subtype.ext
    rw [hαcoe]
    have := D.centralizes_of_ψ_eq_one h n₀.2
    rw [this]
    group
  have hsq : u * u = 1 := Subtype.ext (by simpa [sq] using hVe.2 u u.2)
  have : normEnd α u = u := by
    simp only [normEnd, MonoidHom.mk'_apply, hfix]
    rw [hsq, one_mul]
  rw [← this]
  exact hnorm

include D in
theorem exists_mem_uMod (hp : LocalPts p Y) {w : ↥(coreMod n)}
    (hw : w ∈ suppSub (triSet p)) : ∃ u : ↥V, (u : Γ) ∈ uMod G V φ p ∧ ψ u = w := by
  obtain ⟨v', hv', hv'e⟩ := exists_coreAct_triCyc_mul_inv hp.inj hw
  obtain ⟨a, ha⟩ := D.ψ_surj v'
  obtain ⟨n₀, hn₀⟩ := D.φ_surj (triCyc p)
  have hn₀N : (n₀ : Γ) ∈ nGrp G φ p :=
    mem_preimG.2 ⟨n₀.2, by rw [show φ ⟨(n₀ : Γ), n₀.2⟩ = triCyc p from hn₀];
                           exact Subgroup.mem_zpowers _⟩
  have hc : ⁅(n₀ : Γ), (a : Γ)⁆ ∈ V := by
    have h1 : (n₀ : Γ) * a * (n₀ : Γ)⁻¹ ∈ V := D.conj_mem n₀.2 a.2
    have h2 := V.mul_mem h1 (V.inv_mem a.2)
    simpa [commutatorElement_def, mul_assoc] using h2
  refine ⟨⟨⁅(n₀ : Γ), (a : Γ)⁆, hc⟩, Subgroup.commutator_mem_commutator hn₀N a.2, ?_⟩
  rw [ψ_commutator D n₀.2 (v := a) hc, ha]
  have : φ ⟨(n₀ : Γ), n₀.2⟩ = triCyc p := hn₀
  rw [this]
  exact hv'e

theorem mem_normalizer_nGrp (hp : LocalPts p Y) {l : Γ} (hl : l ∈ preimG G φ Y) :
    l ∈ Subgroup.normalizer (nGrp G φ p : Set Γ) := by
  obtain ⟨hlG, hlY⟩ := mem_preimG.1 hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hnorm := fun (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ Y) =>
    Subgroup.mem_normalizer_iff.mp (hp.normalizes hσ)
  constructor
  · intro hx
    obtain ⟨hxG, hxd⟩ := mem_preimG.1 hx
    have hy : l * x * l⁻¹ ∈ G := G.mul_mem (G.mul_mem hlG hxG) (G.inv_mem hlG)
    refine mem_preimG.2 ⟨hy, ?_⟩
    have e : (⟨l * x * l⁻¹, hy⟩ : ↥G) = ⟨l, hlG⟩ * ⟨x, hxG⟩ * ⟨l, hlG⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact (hnorm _ hlY (φ ⟨x, hxG⟩)).1 hxd
  · intro hx
    obtain ⟨hyG, hyd⟩ := mem_preimG.1 hx
    have hxG : x ∈ G := by
      have := G.mul_mem (G.mul_mem (G.inv_mem hlG) hyG) hlG
      simpa [mul_assoc] using this
    refine mem_preimG.2 ⟨hxG, ?_⟩
    have e : (⟨x, hxG⟩ : ↥G) = ⟨l, hlG⟩⁻¹ * ⟨l * x * l⁻¹, hyG⟩ * ⟨l, hlG⟩ := by
      apply Subtype.ext
      simp [mul_assoc]
    rw [e, map_mul, map_mul, map_inv]
    have hinv : (φ ⟨l, hlG⟩)⁻¹ ∈ Y := Y.inv_mem hlY
    have := (hnorm _ hinv (φ ⟨l * x * l⁻¹, hyG⟩)).1 hyd
    simpa using this

include D in
theorem mem_normalizer_uMod (hp : LocalPts p Y) {l : Γ} (hl : l ∈ preimG G φ Y) :
    l ∈ Subgroup.normalizer (uMod G V φ p : Set Γ) := by
  have hlG : l ∈ G := preimG_le G φ Y hl
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ g ∈ preimG G φ Y, ∀ x ∈ uMod G V φ p, g * x * g⁻¹ ∈ uMod G V φ p := fun g hg x hx =>
    conj_mem_commutator (mem_normalizer_nGrp hp hg) (D.normal (preimG_le G φ Y hg)) hx
  intro x
  refine ⟨key l hl x, fun hx => ?_⟩
  have := key l⁻¹ ((preimG G φ Y).inv_mem hl) _ hx
  simpa [mul_assoc] using this

@[expose] noncomputable def locHom (hp : LocalPts p Y) :
    ↥(preimG G φ Y) →* Equiv.Perm (Fin 3) :=
  (resHom hp.inj).comp
    ((φ.comp (Subgroup.inclusion (preimG_le G φ Y))).codRestrict (setStab (triSet p))
      (fun l => hp.le_stab (mem_preimG.1 l.2).2))

theorem p_locHom (hp : LocalPts p Y) (l : ↥(preimG G φ Y)) (i : Fin 3) :
    p (locHom hp l i) = (φ ⟨(l : Γ), preimG_le G φ Y l.2⟩ : Equiv.Perm (Fin n)) (p i) :=
  p_resHom hp.inj _ i

include D in
@[expose] noncomputable def uHom (hp : LocalPts p Y) : ↥(uMod G V φ p) →* ↥(coreMod 3) :=
  (coordHom hp.inj).comp
    ((ψ.comp (Subgroup.inclusion (uMod_le_V D))).codRestrict (suppSub (triSet p))
      (fun u => (mem_suppV.1 (uMod_le_suppV D u.2)).2))

include D in
theorem uHom_eq (hp : LocalPts p Y) (u : ↥(uMod G V φ p)) :
    uHom D hp u = coordHom hp.inj ⟨ψ ⟨(u : Γ), uMod_le_V D u.2⟩,
      (mem_suppV.1 (uMod_le_suppV D u.2)).2⟩ := rfl

theorem coreAct_eq_of_fixes {σ : Equiv.Perm (Fin n)} (hσ : ∀ j ∈ triSet p, σ j = j)
    {v : ↥(coreMod n)} (hv : v ∈ suppSub (triSet p)) : coreAct n σ v = v := by
  apply vcoord_ext
  intro j
  rw [vcoord_coreAct]
  by_cases hj : j ∈ triSet p
  · have : σ⁻¹ j = j := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact (hσ j hj).symm
    rw [this]
  · have h1 : σ⁻¹ j ∉ triSet p := fun h => hj (by
      have h2 := hσ _ h
      have h3 : σ (σ⁻¹ j) = j := by simp
      rw [h3] at h2
      rw [h2]
      exact h)
    rw [hv j hj, hv _ h1]

include D in
theorem locHom_surjective (hp : LocalPts p Y) :
    Function.Surjective (locHom (G := G) (φ := φ) hp) := by
  classical
  have hinj := hp.inj
  obtain ⟨lt, hlt⟩ := D.φ_surj (Equiv.swap (p 0) (p 2))
  obtain ⟨ld, hld⟩ := D.φ_surj (triCyc p)
  have hltL : (lt : Γ) ∈ preimG G φ Y :=
    mem_preimG.2 ⟨lt.2, by rw [show φ ⟨(lt : Γ), lt.2⟩ = Equiv.swap (p 0) (p 2) from hlt];
                           exact hp.swap_mem⟩
  have hldL : (ld : Γ) ∈ preimG G φ Y :=
    mem_preimG.2 ⟨ld.2, by rw [show φ ⟨(ld : Γ), ld.2⟩ = triCyc p from hld]; exact hp.d_mem⟩
  set a := locHom (G := G) (φ := φ) hp ⟨(lt : Γ), hltL⟩ with ha_def
  set b := locHom (G := G) (φ := φ) hp ⟨(ld : Γ), hldL⟩ with hb_def
  have ha : ∀ i, p (a i) = Equiv.swap (p 0) (p 2) (p i) := fun i => by
    rw [ha_def, p_locHom hp]
    exact congrArg (fun σ : Equiv.Perm (Fin n) => σ (p i)) hlt
  have hb : ∀ i, p (b i) = triCyc p (p i) := fun i => by
    rw [hb_def, p_locHom hp]
    exact congrArg (fun σ : Equiv.Perm (Fin n) => σ (p i)) hld
  have hb' : ∀ i, b i = i + 1 := fun i => hinj (by rw [hb i, triCyc_apply hinj])
  have ha2 : a ^ 2 = 1 := by
    rw [pow_two]
    exact Equiv.ext fun i => hinj (by
      rw [Equiv.Perm.mul_apply, ha, ha]
      exact Equiv.swap_apply_self _ _ _)
  have ha1 : a ≠ 1 := by
    intro h
    have h1 := ha 0
    rw [h, Equiv.Perm.one_apply, Equiv.swap_apply_left] at h1
    exact absurd (hinj h1) (by decide)
  have hb3 : b ^ 3 = 1 := by
    ext i
    simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, hb', Equiv.Perm.one_apply]
    fin_cases i <;> decide
  have hb1 : b ≠ 1 := by
    intro h
    have h1 := hb' 0
    rw [h, Equiv.Perm.one_apply] at h1
    exact absurd h1 (by decide)
  have hrange : (locHom (G := G) (φ := φ) hp).range = ⊤ :=
    perm_three_eq_top ⟨_, rfl⟩ ⟨_, rfl⟩ ha2 ha1 hb3 hb1
  exact MonoidHom.range_eq_top.1 hrange

include D in
theorem ker_locHom (hp : LocalPts p Y) :
    (locHom (G := G) (φ := φ) hp).ker =
      (preimG G φ Y ⊓ Subgroup.centralizer (uMod G V φ p : Set Γ)).subgroupOf
        (preimG G φ Y) := by
  classical
  ext l
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have hlG : (l : Γ) ∈ G := preimG_le G φ Y l.2
  have hσstab : φ ⟨(l : Γ), hlG⟩ ∈ setStab (triSet p) := hp.le_stab (mem_preimG.1 l.2).2
  constructor
  · intro h1
    refine ⟨l.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hfix : ∀ j ∈ triSet p, φ ⟨(l : Γ), hlG⟩ j = j := by
      intro j hj
      obtain ⟨i, rfl⟩ := mem_triSet.1 hj
      have := p_locHom hp l i
      rw [h1, Equiv.Perm.one_apply] at this
      exact this.symm
    have huV : u ∈ V := uMod_le_V D hu
    have hconj : (l : Γ) * u * (l : Γ)⁻¹ ∈ uMod G V φ p :=
      (Subgroup.mem_normalizer_iff.mp (mem_normalizer_uMod D hp l.2) u).mp hu
    have hconjV : (l : Γ) * u * (l : Γ)⁻¹ ∈ V := uMod_le_V D hconj
    have hψ := D.equivar ⟨(l : Γ), hlG⟩ ⟨u, huV⟩ hconjV
    have hsupp : ψ ⟨u, huV⟩ ∈ suppSub (triSet p) := (mem_suppV.1 (uMod_le_suppV D hu)).2
    rw [coreAct_eq_of_fixes hfix hsupp] at hψ
    have hw : ((⟨(l : Γ) * u * (l : Γ)⁻¹, hconjV⟩ * ⟨u, huV⟩⁻¹ : ↥V) : Γ) ∈ uMod G V φ p := by
      show (l : Γ) * u * (l : Γ)⁻¹ * u⁻¹ ∈ uMod G V φ p
      exact (uMod G V φ p).mul_mem hconj ((uMod G V φ p).inv_mem hu)
    have hw1 := eq_one_of_mem_uMod D hp hw (by rw [map_mul, map_inv, hψ]; exact mul_inv_cancel _)
    have hweq : (l : Γ) * u * (l : Γ)⁻¹ = u := by
      have := congrArg Subtype.val (mul_inv_eq_one.1 hw1)
      exact this
    exact (mul_inv_eq_iff_eq_mul.1 hweq).symm
  · rintro ⟨-, hc⟩
    have hfixU : ∀ w ∈ suppSub (triSet p), coreAct n (φ ⟨(l : Γ), hlG⟩) w = w := by
      intro w hw
      obtain ⟨u, hu, hψu⟩ := exists_mem_uMod D hp hw
      have hcomm : (u : Γ) * l = l * u := Subgroup.mem_centralizer_iff.mp hc u hu
      have hconjV : (l : Γ) * u * (l : Γ)⁻¹ ∈ V := D.conj_mem hlG u.2
      have hψ := D.equivar ⟨(l : Γ), hlG⟩ u hconjV
      have h2 : (⟨(l : Γ) * u * (l : Γ)⁻¹, hconjV⟩ : ↥V) = u := Subtype.ext (by
        show (l : Γ) * u * (l : Γ)⁻¹ = u
        rw [← hcomm]
        group)
      rw [h2, hψu] at hψ
      exact hψ.symm
    have hco : coreAct 3 (locHom (G := G) (φ := φ) hp l) = 1 := by
      refine MulEquiv.ext fun v => ?_
      obtain ⟨w, hwv⟩ := (coordHom_bijective hp.inj).2 v
      have hv : coreAct n (φ ⟨(l : Γ), hlG⟩) (w : ↥(coreMod n)) ∈ suppSub (triSet p) :=
        coreAct_mem_suppSub hσstab w.2
      have h := coordHom_coreAct hp.inj (σ := φ ⟨(l : Γ), hlG⟩)
        (τ := locHom (G := G) (φ := φ) hp l) (fun i => (p_locHom hp l i).symm) w hv
      have h3 : (⟨coreAct n (φ ⟨(l : Γ), hlG⟩) (w : ↥(coreMod n)), hv⟩ :
          ↥(suppSub (triSet p))) = w := Subtype.ext (hfixU w w.2)
      rw [h3, hwv] at h
      exact h.symm
    exact coreAct_injective (le_refl 3) (hco.trans (map_one _).symm)

include D in
theorem uHom_surjective (hp : LocalPts p Y) : Function.Surjective (uHom D hp) := by
  intro v
  obtain ⟨w, hwv⟩ := (coordHom_bijective hp.inj).2 v
  obtain ⟨u, hu, hψu⟩ := exists_mem_uMod D hp w.2
  refine ⟨⟨(u : Γ), hu⟩, ?_⟩
  rw [uHom_eq, ← hwv]
  congr 1
  exact Subtype.ext hψu

include D in
theorem ker_uHom (hp : LocalPts p Y) :
    (uHom D hp).ker = (uMod G V φ p ⊓ Subgroup.centralizer (preimG G φ Y : Set Γ)).subgroupOf
      (uMod G V φ p) := by
  classical
  ext u
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have huV : (u : Γ) ∈ V := uMod_le_V D u.2
  have hsupp : ψ ⟨(u : Γ), huV⟩ ∈ suppSub (triSet p) := (mem_suppV.1 (uMod_le_suppV D u.2)).2
  constructor
  · intro h1
    have h2 : ψ ⟨(u : Γ), huV⟩ = 1 := by
      have h3 : coordHom hp.inj ⟨ψ ⟨(u : Γ), huV⟩, hsupp⟩ = coordHom hp.inj 1 := by
        rw [map_one]
        exact h1
      have := (coordHom_bijective hp.inj).1 h3
      exact congrArg Subtype.val this
    have h4 := eq_one_of_mem_uMod D hp (u := ⟨(u : Γ), huV⟩) u.2 h2
    have h5 : (u : Γ) = 1 := congrArg Subtype.val h4
    refine ⟨u.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l _
    rw [h5, mul_one, one_mul]
  · rintro ⟨-, hc⟩
    obtain ⟨l₀, hl₀⟩ := D.φ_surj (triCyc p)
    have hl₀L : (l₀ : Γ) ∈ preimG G φ Y :=
      mem_preimG.2 ⟨l₀.2, by rw [show φ ⟨(l₀ : Γ), l₀.2⟩ = triCyc p from hl₀]; exact hp.d_mem⟩
    have hcomm : (l₀ : Γ) * u = u * l₀ := Subgroup.mem_centralizer_iff.mp hc l₀ hl₀L
    have hconjV : (l₀ : Γ) * u * (l₀ : Γ)⁻¹ ∈ V := D.conj_mem l₀.2 huV
    have hψ := D.equivar l₀ ⟨(u : Γ), huV⟩ hconjV
    have h2 : (⟨(l₀ : Γ) * u * (l₀ : Γ)⁻¹, hconjV⟩ : ↥V) = ⟨(u : Γ), huV⟩ := Subtype.ext (by
      show (l₀ : Γ) * u * (l₀ : Γ)⁻¹ = u
      exact mul_inv_eq_iff_eq_mul.2 hcomm)
    rw [h2, hl₀] at hψ
    have h3 : ψ ⟨(u : Γ), huV⟩ = 1 :=
      eq_one_of_coreAct_triCyc_eq hp.inj hsupp hψ.symm
    rw [uHom_eq]
    have : (⟨ψ ⟨(u : Γ), huV⟩, hsupp⟩ : ↥(suppSub (triSet p))) = 1 := Subtype.ext h3
    rw [this, map_one]

include D in
theorem uHom_equivar (hp : LocalPts p Y) (l : ↥(preimG G φ Y)) (u : ↥(uMod G V φ p))
    (hw : (l : Γ) * u * (l : Γ)⁻¹ ∈ uMod G V φ p) :
    uHom D hp ⟨(l : Γ) * u * (l : Γ)⁻¹, hw⟩ =
      coreAct 3 (locHom (G := G) (φ := φ) hp l) (uHom D hp u) := by
  classical
  have hlG : (l : Γ) ∈ G := preimG_le G φ Y l.2
  have hσstab : φ ⟨(l : Γ), hlG⟩ ∈ setStab (triSet p) := hp.le_stab (mem_preimG.1 l.2).2
  have huV : (u : Γ) ∈ V := uMod_le_V D u.2
  have hconjV : (l : Γ) * u * (l : Γ)⁻¹ ∈ V := uMod_le_V D hw
  have hsupp : ψ ⟨(u : Γ), huV⟩ ∈ suppSub (triSet p) := (mem_suppV.1 (uMod_le_suppV D u.2)).2
  have hsupp' : ψ ⟨(l : Γ) * u * (l : Γ)⁻¹, hconjV⟩ ∈ suppSub (triSet p) :=
    (mem_suppV.1 (uMod_le_suppV D hw)).2
  have hψ := D.equivar ⟨(l : Γ), hlG⟩ ⟨(u : Γ), huV⟩ hconjV
  have hv : coreAct n (φ ⟨(l : Γ), hlG⟩) (ψ ⟨(u : Γ), huV⟩) ∈ suppSub (triSet p) :=
    coreAct_mem_suppSub hσstab hsupp
  have h := coordHom_coreAct hp.inj (σ := φ ⟨(l : Γ), hlG⟩)
    (τ := locHom (G := G) (φ := φ) hp l) (fun i => (p_locHom hp l i).symm)
    ⟨ψ ⟨(u : Γ), huV⟩, hsupp⟩ hv
  rw [uHom_eq, uHom_eq]
  rw [← h]
  congr 1
  exact Subtype.ext hψ

include D in
theorem isNatSym_local (hp : LocalPts p Y) : IsNatSym (preimG G φ Y) (uMod G V φ p) 3 :=
  ⟨locHom hp, uHom D hp, locHom_surjective D hp, ker_locHom D hp, uHom_surjective D hp,
    ker_uHom D hp, fun l u hw => uHom_equivar D hp l u hw⟩

end Local

end CFSG.CGT.PushingUpLit.BHS6
