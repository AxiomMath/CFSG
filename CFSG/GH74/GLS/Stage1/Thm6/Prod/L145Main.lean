module

public import CFSG.GH74.GLS.Stage1.Thm6.Prod.L145Pgl
public import CFSG.GH74.GLS.Stage2.Local.Defs
import CFSG.GH74.GLS.Stage1.Main.P49HBase
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.L145K0

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Prod.L145

open Subgroup CFSG CFSG.GorensteinWalter DihedralGroup
open scoped commutatorElement

theorem d8_closure : ∀ g : DihedralGroup 4,
    g ∈ Subgroup.closure ({sr 0, sr 1} : Set (DihedralGroup 4)) := by
  intro g
  have h0 : (sr 0 : DihedralGroup 4) ∈ Subgroup.closure ({sr 0, sr 1} : Set (DihedralGroup 4)) :=
    Subgroup.subset_closure (by simp)
  have h1 : (sr 1 : DihedralGroup 4) ∈ Subgroup.closure ({sr 0, sr 1} : Set (DihedralGroup 4)) :=
    Subgroup.subset_closure (by simp)
  set S := Subgroup.closure ({sr 0, sr 1} : Set (DihedralGroup 4))
  have hr1 : (r 1 : DihedralGroup 4) ∈ S := by
    have : (r 1 : DihedralGroup 4) = sr 0 * sr 1 := by decide
    rw [this]; exact S.mul_mem h0 h1
  have hr2 : (r 2 : DihedralGroup 4) ∈ S := by
    have : (r 2 : DihedralGroup 4) = r 1 * r 1 := by decide
    rw [this]; exact S.mul_mem hr1 hr1
  have hr3 : (r 3 : DihedralGroup 4) ∈ S := by
    have : (r 3 : DihedralGroup 4) = r 2 * r 1 := by decide
    rw [this]; exact S.mul_mem hr2 hr1
  have hr0 : (r 0 : DihedralGroup 4) ∈ S := by
    have : (r 0 : DihedralGroup 4) = 1 := by decide
    rw [this]; exact S.one_mem
  have hs2 : (sr 2 : DihedralGroup 4) ∈ S := by
    have : (sr 2 : DihedralGroup 4) = sr 0 * r 2 := by decide
    rw [this]; exact S.mul_mem h0 hr2
  have hs3 : (sr 3 : DihedralGroup 4) ∈ S := by
    have : (sr 3 : DihedralGroup 4) = sr 0 * r 3 := by decide
    rw [this]; exact S.mul_mem h0 hr3
  rcases g with i | i
  · fin_cases i
    · exact hr0
    · exact hr1
    · exact hr2
    · exact hr3
  · fin_cases i
    · exact h0
    · exact h1
    · exact hs2
    · exact hs3

structure Cfg {X : Type} [Group X] [Finite X] (x : X) [CentralInv x] (ψ : DihedralGroup 4 →* X)
    (T : Sylow 2 X) (P : X → Prop) : Prop where
  dih : DihData x ψ T
  fa : ∃ c : X, c * ψ (r 2) * c⁻¹ = ψ (sr 1)
  fb : ∃ c : X, c * ψ (r 2) * c⁻¹ = ψ (sr 3)
  nonsolv : ¬ Group.IsSolvable X
  Px : P x
  Py : P (ψ (sr 0))
  Pyx : P (ψ (sr 0) * x)
  Pzx : P (ψ (r 2) * x)
  nPz : ¬ P (ψ (r 2))
  Pconj : ∀ g u : X, P u → P (g * u * g⁻¹)

@[expose] def NC (X : Type) [Group X] [Finite X] (x : X) (P : X → Prop) : Prop :=
  ∃ (K : Subgroup X) (y : X) (q : ℕ), IsPComponent 2 K ∧
    IVK.IsL2 (↥K ⧸ pPrimeCore 2 ↥K) (fun r => r = q) ∧ (q % 8 = 3 ∨ q % 8 = 5) ∧
    orderOf y = 2 ∧ GLS.Stage2.Local.PGLModO K (zpowers y) q ∧ zpowers x ⊓ (K ⊔ zpowers y) = ⊥ ∧
    oPrimeResidual 2 X ⊔ pPrimeCore 2 X = pPrimeCore 2 X ⊔ zpowers x ⊔ (K ⊔ zpowers y) ∧
    ∀ u : X, orderOf u = 2 → u ∉ K → P u

section Sup

variable {H : Type} [Group H] [Finite H] {L : Subgroup H}

theorem Lc_sup_eq (hcard2 : Nat.card L = 2 * Nat.card (Lc L)) {u : H} (hu : u ∈ L)
    (hu' : u ∉ Lc L) : Lc L ⊔ zpowers u = L := by
  have hle : Lc L ⊔ zpowers u ≤ L := sup_le Lc_le ((Subgroup.zpowers_le).2 hu)
  have hsub : Lc L ≤ Lc L ⊔ zpowers u := le_sup_left
  have h1 : Lc L < Lc L ⊔ zpowers u := by
    refine lt_of_le_of_ne hsub fun h => hu' ?_
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hd1 : Nat.card (Lc L) ∣ Nat.card ↥(Lc L ⊔ zpowers u) := Subgroup.card_dvd_of_le hsub
  have hd2 : Nat.card ↥(Lc L ⊔ zpowers u) ∣ Nat.card L := Subgroup.card_dvd_of_le hle
  have hlt : Nat.card (Lc L) < Nat.card ↥(Lc L ⊔ zpowers u) := by
    by_contra hnot
    push Not at hnot
    exact (ne_of_lt h1) (Subgroup.eq_of_le_of_card_ge hsub hnot)
  have hpos : 0 < Nat.card (Lc L) := Nat.card_pos
  obtain ⟨t, ht⟩ := hd1
  have ht2 : t ∣ 2 := by
    rw [ht, hcard2] at hd2
    have : Nat.card (Lc L) * t ∣ Nat.card (Lc L) * 2 := by rwa [mul_comm 2] at hd2
    exact (Nat.mul_dvd_mul_iff_left hpos).1 this
  have ht_le : t ≤ 2 := Nat.le_of_dvd (by norm_num) ht2
  have ht_gt : 1 < t := by
    by_contra h
    push Not at h
    interval_cases t
    · simp at ht; omega
    · simp at ht; omega
  have ht' : t = 2 := by omega
  have hcardM : Nat.card ↥(Lc L ⊔ zpowers u) = Nat.card L := by rw [ht, ht', hcard2, mul_comm]
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardM.symm)

end Sup

section Pgl

variable {X : Type} [Group X] [Finite X] {x : X} [CentralInv x] {ψ : DihedralGroup 4 →* X}
  {T : Sylow 2 X} {P : X → Prop}

omit [Finite X] [CentralInv x] in
theorem orderOf_psi_sr (hD : DihData x ψ T) (i : ZMod 4) : orderOf (ψ (sr i)) = 2 := by
  rw [orderOf_injective ψ hD.inj]
  exact orderOf_eq_prime (by rw [pow_two, sr_mul_self]) (by rw [DihedralGroup.one_def]; exact fun h => by cases h)

omit [Finite X] [CentralInv x] in
theorem orderOf_psi_r2 (hD : DihData x ψ T) : orderOf (ψ (r 2)) = 2 := by
  rw [orderOf_injective ψ hD.inj]
  exact orderOf_eq_prime (by rw [pow_two]; decide) (by decide)

omit [Finite X] in
theorem psi_sr_sq (i : ZMod 4) : ψ (sr i) * ψ (sr i) = 1 := by
  rw [← map_mul, sr_mul_self, map_one]

omit [Finite X] in
theorem psi_comm : ⁅ψ (sr 0), ψ (sr 1)⁆ = ψ (r 2) := by
  rw [← map_commutatorElement]
  congr 1

variable {K : Type} [Field K] [Finite K] {L : Subgroup (Qh x)} [L.Normal]

theorem pi_mem_L (hLodd : Odd L.index) {g : X} (hg : g * g = 1) : piH x g ∈ L := by
  refine two_elt_mem_L hLodd (m := 1) ?_
  rw [pow_one, pow_two, ← map_mul, hg, map_one]

theorem pi_z_mem_Lc (hLodd : Odd L.index) : piH x (ψ (r 2)) ∈ Lc L := by
  have hy := pi_mem_L (L := L) hLodd (psi_sr_sq (ψ := ψ) 0)
  have ha := pi_mem_L (L := L) hLodd (psi_sr_sq (ψ := ψ) 1)
  let yL : ↥L := ⟨piH x (ψ (sr 0)), hy⟩
  let aL : ↥L := ⟨piH x (ψ (sr 1)), ha⟩
  have hcomm : ⁅yL, aL⁆ ∈ commutator ↥L :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have h1 : ((⁅yL, aL⁆ : ↥L) : Qh x) = piH x (ψ (r 2)) := by
    rw [← psi_comm (ψ := ψ), map_commutatorElement]
    simp [yL, aL, commutatorElement_def]
  rw [← h1]
  exact (mem_Lc_iff _).2 hcomm

theorem pi_a_mem_Lc (hc : Cfg x ψ T P) (hLodd : Odd L.index) : piH x (ψ (sr 1)) ∈ Lc L := by
  obtain ⟨c, hc'⟩ := hc.fa
  rw [← hc', map_mul, map_mul]
  exact (Lc_normal (L := L)).conj_mem _ (pi_z_mem_Lc hLodd) _

theorem pi_y_not_mem_Lc (hc : Cfg x ψ T P) (hLodd : Odd L.index)
    (hLc : ∃ m', Odd m' ∧ Nat.card (Lc L) = 4 * m') : piH x (ψ (sr 0)) ∉ Lc L := by
  intro hy
  let f : DihedralGroup 4 →* Qh x := (piH x).comp ψ
  have hall : ∀ g : DihedralGroup 4, f g ∈ Lc L := by
    intro g
    have hcl : Subgroup.closure ({sr 0, sr 1} : Set (DihedralGroup 4)) ≤ (Lc L).comap f := by
      rw [Subgroup.closure_le]
      intro g hg
      rcases hg with rfl | rfl
      · exact hy
      · exact pi_a_mem_Lc hc hLodd
    exact hcl (d8_closure g)
  let f' : DihedralGroup 4 →* ↥(Lc L) := f.codRestrict (Lc L) hall
  have hinj : Function.Injective f' := fun a b hab =>
    hc.dih.piPsi_injective (congrArg Subtype.val hab)
  have hdvd : Nat.card (DihedralGroup 4) ∣ Nat.card (Lc L) := Subgroup.card_dvd_of_injective f' hinj
  rw [DihedralGroup.nat_card] at hdvd
  obtain ⟨m', hm', hcard⟩ := hLc
  rw [hcard] at hdvd
  have : 2 ∣ m' := by omega
  exact (Nat.not_even_iff_odd.2 hm') (even_iff_two_dvd.2 this)

end Pgl

section Clauses

variable {X : Type} [Group X] [Finite X] {x : X} [CentralInv x]

omit [Finite X] [CentralInv x] in
theorem mem_zpowers_of_orderOf_two {g s : X} (hg : orderOf g = 2) (hs : s ∈ zpowers g) :
    s = 1 ∨ s = g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
  have hk : g ^ k = g ^ (k % 2) := by
    rw [← zpow_mod_orderOf, hg]; rfl
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left; rw [hk, h0]; simp
  · right; rw [hk, h1]; simp

theorem ker_restrict_sup {Lc : Subgroup (Qh x)} [Lc.Normal] [Group.IsPerfect ↥Lc]
    (hxK : x ∉ K0 x Lc) {y : X} (hy2 : orderOf y = 2) (hynot : piH x y ∉ Lc) {g : X}
    (hg : g ∈ K0 x Lc ⊔ zpowers y) (hπ : piH x g = 1) : g ∈ K0 x Lc ⊓ pPrimeCore 2 X := by
  obtain ⟨k, hk, s, hs, hks⟩ := Subgroup.mem_sup_of_normal_left.1 hg
  rcases mem_zpowers_of_orderOf_two hy2 hs with hs1 | hs1
  · rw [hs1, mul_one] at hks
    rw [← hks] at hπ ⊢
    exact ⟨hk, ker_inf_le hxK ⟨hk, hπ⟩⟩
  · exfalso
    rw [hs1] at hks
    rw [← hks, map_mul] at hπ
    have h1 : piH x k ∈ Lc := by
      have : piH x k ∈ (K0 x Lc).map (piH x) := ⟨k, hk, rfl⟩
      rwa [K0_map] at this
    have : piH x y = (piH x k)⁻¹ := eq_inv_of_mul_eq_one_right hπ
    exact hynot (this ▸ Lc.inv_mem h1)

theorem pglModO_K0 {Lc L : Subgroup (Qh x)} [Lc.Normal] [Group.IsPerfect ↥Lc]
    (hxK : x ∉ K0 x Lc) {y : X} (hy2 : orderOf y = 2) (hynot : piH x y ∉ Lc)
    (hsup : Lc ⊔ zpowers (piH x y) = L) {K : Type} [Field K] [Finite K] (e : ↥L ≃* PGL2 K) :
    GLS.Stage2.Local.PGLModO (K0 x Lc) (zpowers y) (Nat.card K) := by
  have hOK : GLS.pPrimeCoreOf 2 (K0 x Lc) = pPrimeCore 2 X ⊓ K0 x Lc :=
    pPrimeCore_map_normal (K0 x Lc)
  let ρ : ↥(K0 x Lc ⊔ zpowers y) →* Qh x := (piH x).comp (K0 x Lc ⊔ zpowers y).subtype
  have hrange : ρ.range = L := by
    rw [← hsup]
    show ((piH x).comp (K0 x Lc ⊔ zpowers y).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_sup, K0_map,
      MonoidHom.map_zpowers]
  have hker : ρ.ker = (pPrimeCore 2 X ⊓ K0 x Lc).subgroupOf (K0 x Lc ⊔ zpowers y) := by
    ext g
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      have := ker_restrict_sup hxK hy2 hynot g.2 hg
      exact ⟨this.2, this.1⟩
    · intro hg
      have h3 : (g : X) ∈ (piH x).ker := by
        rw [ker_piH]; exact Subgroup.mem_sup_left hg.1
      exact h3
  have hnorm : ((GLS.pPrimeCoreOf 2 (K0 x Lc)).subgroupOf (K0 x Lc ⊔ zpowers y)).Normal := by
    rw [hOK]; exact Subgroup.Normal.subgroupOf inferInstance _
  refine ⟨hnorm, K, inferInstance, inferInstance, rfl, ⟨?_⟩⟩
  have hker' : ρ.ker = (GLS.pPrimeCoreOf 2 (K0 x Lc)).subgroupOf (K0 x Lc ⊔ zpowers y) := by
    rw [hOK]; exact hker
  exact (QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
    ((QuotientGroup.quotientKerEquivRange ρ).trans ((MulEquiv.subgroupCongr hrange).trans e))

theorem x_inf_sup_eq_bot {Lc : Subgroup (Qh x)} [Lc.Normal] [Group.IsPerfect ↥Lc]
    (hxK : x ∉ K0 x Lc) {y : X} (hy2 : orderOf y = 2) (hynot : piH x y ∉ Lc) :
    zpowers x ⊓ (K0 x Lc ⊔ zpowers y) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgx, hgA⟩
  rcases CentralInv.mem_zpowers hgx with h1 | h1
  · rw [h1]; exact Subgroup.one_mem _
  · exfalso
    rw [h1] at hgA
    have hπ : piH x x = 1 := by
      have : x ∈ (piH x).ker := by rw [ker_piH]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
      exact this
    exact hxK (ker_restrict_sup hxK hy2 hynot hgA hπ).1

omit [CentralInv x] in
theorem le_oPrimeResidual_of_perfect {Kb : Subgroup X} (hP : Group.IsPerfect ↥Kb) :
    Kb ≤ oPrimeResidual 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (oPrimeResidual 2 X).Normal := Stage1.Thm3.Sec6.P49H.oPrimeResidual_two_normal X
  set M : Subgroup ↥Kb := (oPrimeResidual 2 X).subgroupOf Kb with hM
  have : M.Normal := Subgroup.Normal.subgroupOf inferInstance Kb
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥Kb) := inferInstance
  have hSM : (S : Subgroup ↥Kb) ≤ M := by
    intro y hy
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨y, hy⟩
    refine Subgroup.subset_closure ⟨k, ?_⟩
    have := congrArg (fun z : ↥S => ((z : ↥Kb) : X)) hk
    simpa using this
  have hodd : Odd M.index := by
    have h1 : M.index ∣ (S : Subgroup ↥Kb).index := Subgroup.index_dvd_of_le hSM
    have h2 : ¬ 2 ∣ (S : Subgroup ↥Kb).index := S.not_dvd_index
    exact Odd.of_dvd_nat (Nat.odd_iff.2 (by omega)) h1
  have : Group.IsPerfect (↥Kb ⧸ M) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective M)
  have : Group.IsSolvable (↥Kb ⧸ M) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hsub : Subsingleton (↥Kb ⧸ M) := by
    by_contra hns
    have : Nontrivial (↥Kb ⧸ M) := not_subsingleton_iff_nontrivial.1 hns
    have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial (↥Kb ⧸ M)
    rw [Group.IsPerfect.commutator_eq_top] at h1
    exact lt_irrefl _ h1
  have hMtop : M = ⊤ := by
    rw [← Subgroup.index_eq_one]
    have : Nat.card (↥Kb ⧸ M) = 1 := Nat.card_unique
    exact this
  intro y hy
  have : (⟨y, hy⟩ : ↥Kb) ∈ M := hMtop ▸ Subgroup.mem_top _
  exact this

theorem clause7 {Lc L : Subgroup (Qh x)} [Lc.Normal] [Group.IsPerfect ↥Lc] [L.Normal] (hLodd : Odd L.index)
    {y : X} (hy2 : orderOf y = 2) (hsup : Lc ⊔ zpowers (piH x y) = L) :
    oPrimeResidual 2 X ⊔ pPrimeCore 2 X =
      pPrimeCore 2 X ⊔ zpowers x ⊔ (K0 x Lc ⊔ zpowers y) := by
  have hy : y ^ (2 ^ 1) = 1 := by rw [pow_one]; exact hy2 ▸ pow_orderOf_eq_one y
  have hxx : x ^ (2 ^ 1) = 1 := by rw [pow_one, pow_two, CentralInv.sq (x := x)]
  apply le_antisymm
  · refine sup_le ?_ (le_sup_of_le_left le_sup_left)
    unfold oPrimeResidual
    rw [Subgroup.closure_le]
    rintro g ⟨k, hk⟩
    have hgL : piH x g ∈ L := two_elt_mem_L hLodd (m := k) (by rw [← map_pow, hk, map_one])
    have hmem : piH x g ∈ (K0 x Lc ⊔ zpowers y).map (piH x) := by
      rw [Subgroup.map_sup, K0_map, MonoidHom.map_zpowers, hsup]; exact hgL
    obtain ⟨r, hr, hrg⟩ := hmem
    have hker : g * r⁻¹ ∈ (piH x).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← hrg, mul_inv_cancel]
    rw [ker_piH] at hker
    have hg : g = (g * r⁻¹) * r := by group
    show g ∈ (pPrimeCore 2 X ⊔ zpowers x ⊔ (K0 x Lc ⊔ zpowers y) : Subgroup X)
    rw [hg]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hker) (Subgroup.mem_sup_right hr)
  · have hW : ∀ {z : X}, z ^ (2 ^ 1) = 1 → zpowers z ≤ oPrimeResidual 2 X ⊔ pPrimeCore 2 X :=
      fun {z} hz => by
      have hzW : z ∈ oPrimeResidual 2 X := Subgroup.subset_closure ⟨1, hz⟩
      exact (Subgroup.zpowers_le.2 hzW).trans le_sup_left
    refine sup_le (sup_le le_sup_right (hW hxx)) (sup_le ?_ (hW hy))
    exact (le_oPrimeResidual_of_perfect K0_perfect).trans le_sup_left

omit [Finite X] in
theorem orderOf_dvd_card_O [Finite X] {k : X} (hk : k ∈ pPrimeCore 2 X) : ¬ orderOf k = 2 := by
  intro h
  have hd : orderOf k ∣ Nat.card (pPrimeCore 2 X) := by
    have := orderOf_dvd_natCard (⟨k, hk⟩ : pPrimeCore 2 X)
    rwa [Subgroup.orderOf_mk] at this
  rw [h] at hd
  exact (Nat.not_even_iff_odd.2 (odd_card_pPrimeCore X)) (even_iff_two_dvd.2 hd)

theorem orderOf_pi_eq_two {Lc : Subgroup (Qh x)} [Lc.Normal] [Group.IsPerfect ↥Lc]
    (hxK : x ∉ K0 x Lc) {k : X} (hk : k ∈ K0 x Lc) (hk2 : orderOf k = 2) :
    orderOf (piH x k) = 2 := by
  have hsq : k * k = 1 := by rw [← pow_two]; exact hk2 ▸ pow_orderOf_eq_one k
  refine orderOf_eq_prime (by rw [pow_two, ← map_mul, hsq, map_one]) fun h1 => ?_
  exact orderOf_dvd_card_O (ker_inf_le hxK ⟨hk, h1⟩) hk2

end Clauses

section Last

variable {X : Type} [Group X] [Finite X] {x : X} [CentralInv x] {ψ : DihedralGroup 4 →* X}
  {T : Sylow 2 X} {P : X → Prop}

theorem z_mem_K0 {Lc : Subgroup (Qh x)} [Lc.Normal] [Group.IsPerfect ↥Lc]
    (hxc : x ∉ commutator X) (hz : piH x (ψ (r 2)) ∈ Lc) : ψ (r 2) ∈ K0 x Lc := by
  have hzc : ψ (r 2) ∈ commutator X := by
    rw [← psi_comm (ψ := ψ)]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hz2 : ψ (r 2) ^ (2 ^ 1) = 1 := by
    rw [pow_one, pow_two, ← map_mul]
    have : (r 2 : DihedralGroup 4) * r 2 = 1 := by decide
    rw [this, map_one]
  rcases two_elt_K0 (hz : ψ (r 2) ∈ Lc.comap (piH x)) hz2 with h | h
  · exact h
  · exfalso
    apply hxc
    have h1 : ψ (r 2) * x ∈ commutator X := K0_le_commutator h
    have : x = (ψ (r 2))⁻¹ * (ψ (r 2) * x) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hzc) h1

theorem last_clause (hc : Cfg x ψ T P) {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) {L : Subgroup (Qh x)} [L.Normal]
    (hLodd : Odd L.index) (e : ↥L ≃* PGL2 K) (e1 : ↥(Lc L) ≃* PSL2 K)
    [Group.IsPerfect ↥(Lc L)] (hxc : x ∉ commutator X) (hxK : x ∉ K0 x (Lc L))
    (hynot : piH x (ψ (sr 0)) ∉ Lc L) :
    ∀ u : X, orderOf u = 2 → u ∉ K0 x (Lc L) → P u := by
  have : (Lc L).Normal := Lc_normal
  intro u hu2 huK
  have hsq : ∀ {g : X}, orderOf g = 2 → g * g = 1 := fun {g} hg => by
    rw [← pow_two]; exact hg ▸ pow_orderOf_eq_one g
  have huu : u * u = 1 := hsq hu2
  have huL : piH x u ∈ L := pi_mem_L hLodd huu
  by_cases hN : piH x u ∈ Lc L
  · have hu1 : u ^ (2 ^ 1) = 1 := by rw [pow_one, pow_two]; exact huu
    rcases two_elt_K0 (x := x) (Lc := Lc L) hN hu1 with h | h
    · exact absurd h huK
    · have hww : (u * x) * (u * x) = 1 := by
        calc (u * x) * (u * x) = u * (x * u) * x := by group
          _ = u * (u * x) * x := by rw [(CentralInv.comm (x := x) u).symm]
          _ = (u * u) * (x * x) := by group
          _ = 1 := by rw [huu, CentralInv.sq (x := x), one_mul]
      by_cases hw1 : u * x = 1
      · have : u = x := by
          have := eq_inv_of_mul_eq_one_left hw1
          rw [this]; exact inv_eq_of_mul_eq_one_right (CentralInv.sq (x := x))
        rw [this]; exact hc.Px
      · have hw2 : orderOf (u * x) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hww) hw1
        have hz := z_mem_K0 (ψ := ψ) hxc (pi_z_mem_Lc (x := x) (ψ := ψ) hLodd)
        have hz2 : orderOf (ψ (r 2)) = 2 := orderOf_psi_r2 hc.dih
        have hπw : piH x (u * x) ∈ Lc L := by
          have : piH x (u * x) ∈ (K0 x (Lc L)).map (piH x) := ⟨_, h, rfl⟩
          rwa [K0_map] at this
        have hπz : piH x (ψ (r 2)) ∈ Lc L := pi_z_mem_Lc hLodd
        have hπw2 := orderOf_pi_eq_two hxK h hw2
        have hπz2 := orderOf_pi_eq_two hxK hz hz2
        obtain ⟨l, hl, hlw⟩ := inner_conj hK e1 hπw hπz hπw2 hπz2
        have hl' : l ∈ (K0 x (Lc L)).map (piH x) := by rw [K0_map]; exact hl
        obtain ⟨k, hk, hkl⟩ := hl'
        have hconj : piH x (k * (u * x) * k⁻¹) = piH x (ψ (r 2)) := by
          rw [map_mul, map_mul, map_inv, hkl]; exact hlw
        rcases conj_lift x hw2 hz2 hconj with h1 | h1
        · obtain ⟨g, hg⟩ := isConj_iff.1 h1
          have hgu : g⁻¹ * (ψ (r 2) * x) * g⁻¹⁻¹ = u := by
            have h2 : g⁻¹ * ψ (r 2) * g = u * x := by
              rw [← hg]; group
            calc g⁻¹ * (ψ (r 2) * x) * g⁻¹⁻¹ = g⁻¹ * ψ (r 2) * (x * g) := by group
              _ = g⁻¹ * ψ (r 2) * (g * x) := by rw [(CentralInv.comm (x := x) g).symm]
              _ = (g⁻¹ * ψ (r 2) * g) * x := by group
              _ = (u * x) * x := by rw [h2]
              _ = u * (x * x) := by group
              _ = u := by rw [CentralInv.sq (x := x), mul_one]
          rw [← hgu]
          exact hc.Pconj _ _ hc.Pzx
        · exfalso
          obtain ⟨g, hg⟩ := isConj_iff.1 h1
          have hux : u * x * x = u := by
            rw [mul_assoc, CentralInv.sq (x := x), mul_one]
          rw [hux] at hg
          have hu' : u = g⁻¹ * ψ (r 2) * g⁻¹⁻¹ := by rw [← hg]; group
          exact huK (hu' ▸ (K0_normal (x := x) (Lc := Lc L)).conj_mem _ hz _)
  · have hy_mem : piH x (ψ (sr 0)) ∈ L := pi_mem_L hLodd (psi_sr_sq 0)
    have hπu2 : orderOf (piH x u) = 2 :=
      orderOf_eq_prime (by rw [pow_two, ← map_mul, huu, map_one]) (fun h => hN (by rw [h]; exact (Lc L).one_mem))
    have hπy2 : orderOf (piH x (ψ (sr 0))) = 2 :=
      orderOf_eq_prime (by rw [pow_two, ← map_mul, psi_sr_sq, map_one])
        (fun h => hynot (by rw [h]; exact (Lc L).one_mem))
    obtain ⟨l, hl, hlu⟩ := outer_conj hK hcard e hy_mem huL hπy2 hπu2 hynot hN
    obtain ⟨c, hc'⟩ := piH_surjective x l
    have hconj : piH x (c * ψ (sr 0) * c⁻¹) = piH x u := by
      rw [map_mul, map_mul, map_inv, hc']; exact hlu
    rcases conj_lift x (orderOf_psi_sr hc.dih 0) hu2 hconj with h1 | h1
    · obtain ⟨g, hg⟩ := isConj_iff.1 h1
      rw [← hg]; exact hc.Pconj g _ hc.Py
    · obtain ⟨g, hg⟩ := isConj_iff.1 h1
      rw [← hg]; exact hc.Pconj g _ hc.Pyx

theorem main_pgl2 (hc : Cfg x ψ T P) {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) {L : Subgroup (Qh x)} [L.Normal]
    (hLodd : Odd L.index) (e : ↥L ≃* PGL2 K) (h8 : ∃ m, Odd m ∧ Nat.card (Qh x) = 8 * m) :
    NC X x P := by
  obtain ⟨m, hm, hHm⟩ := h8
  obtain ⟨m', hm', hLm'⟩ := card_eight_mul hLodd hm (by rw [Subgroup.card_mul_index, hHm])
  have hL2 := card_L hK hcard e
  have hLc : ∃ m'', Odd m'' ∧ Nat.card (Lc L) = 4 * m'' := ⟨m', hm', by omega⟩
  have hq8 : Nat.card K % 8 = 3 ∨ Nat.card K % 8 = 5 := by
    refine mod8_of_not_dvd_sixteen (odd_of_isOddPrimePower hK) fun h16 => ?_
    have h1 : Nat.card L = Nat.card K * (Nat.card K ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, pgl2_card_formula]
    rw [← h1, hLm'] at h16
    have : 2 ∣ m' := by omega
    exact (Nat.not_even_iff_odd.2 hm') (even_iff_two_dvd.2 this)
  obtain ⟨e1⟩ := Lc_equiv hK hcard e
  have : (Lc L).Normal := Lc_normal
  have : Group.IsPerfect ↥(Lc L) := Lc_perfect hcard e1
  have : IsSimpleGroup ↥(Lc L) := Lc_simple hcard e1
  have hxc : x ∉ commutator X := by
    have hD := hc.dih
    refine x_not_mem_commutator x T (D := ψ.range) ?_ hD.disj hD.sup.symm
    rw [hD.sup]; exact le_sup_right
  have hxK : x ∉ K0 x (Lc L) := fun h => hxc (K0_le_commutator h)
  have hy2 : orderOf (ψ (sr 0)) = 2 := orderOf_psi_sr hc.dih 0
  have hynot : piH x (ψ (sr 0)) ∉ Lc L := pi_y_not_mem_Lc hc hLodd hLc
  have hy_mem : piH x (ψ (sr 0)) ∈ L := pi_mem_L hLodd (psi_sr_sq 0)
  have hsup : Lc L ⊔ zpowers (piH x (ψ (sr 0))) = L := Lc_sup_eq hL2 hy_mem hynot
  refine ⟨K0 x (Lc L), ψ (sr 0), Nat.card K, K0_isPComponent hxK, ?_, hq8, hy2,
    pglModO_K0 hxK hy2 hynot hsup e, x_inf_sup_eq_bot hxK hy2 hynot, clause7 hLodd hy2 hsup,
    last_clause hc hK hcard hLodd e e1 hxc hxK hynot⟩
  exact ⟨K, inferInstance, inferInstance, rfl,
    ⟨((K0_quot hxK).some.trans e1).trans (IVK.L2.equivPSL K).symm⟩⟩

end Last

end CFSG.GH74.GLS.Stage1.Thm6.Prod.L145
