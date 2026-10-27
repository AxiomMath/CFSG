module


import TauCeti.GroupTheory.QuotientGroup.MulAut
import CFSG.Monster.B.TwoA.Base.SymFiveAut
import CFSG.Quasithin.EmptyFaithful.T1521SA5Wr
import CFSG.Quasithin.EmptyFaithful.S152Y05
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

noncomputable def conjOnQuotient (N : Subgroup G) [N.Normal] :
    G →* MulAut (N ⧸ Subgroup.center N) :=
  letI : (Subgroup.center N).Characteristic := Subgroup.centerCharacteristic
  (MulAut.mapQuotient (Subgroup.center N)).comp (MulAut.conjNormal (H := N))

theorem mem_centralizer_of_conjNormal_div_mem_center [Finite G] {N : Subgroup G} [N.Normal]
    {a : G}
    (hgen : Subgroup.closure {x : N | x ^ 2 = 1} = ⊤)
    (hZodd : Odd (Nat.card (Subgroup.center N)))
    (ha : ∀ n : N, (MulAut.conjNormal (H := N) a) n / n ∈ Subgroup.center N) :
    a ∈ Subgroup.centralizer (N : Set G) := by
  classical
  let K : Subgroup N := (Subgroup.centralizer ({a} : Set G)).comap N.subtype
  have hmem : ∀ x : N, x ^ 2 = 1 → x ∈ K := by
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    let c : N := (MulAut.conjNormal (H := N) a) x / x
    have hc : c ∈ Subgroup.center N := ha x
    have hcx : c * x = (MulAut.conjNormal (H := N) a) x := by
      simp [c, div_eq_mul_inv, mul_assoc]
    have hcomm : Commute c x := (Subgroup.mem_center_iff.mp hc x).symm
    have hpow := hcomm.mul_pow 2
    have h1 : ((MulAut.conjNormal (H := N) a) x) ^ 2 = 1 := by
      simpa [map_pow] using congrArg (MulAut.conjNormal (H := N) a) hx
    have hc2 : c ^ 2 = 1 := by
      rw [hcx, h1, hx, mul_one] at hpow
      exact hpow.symm
    have hc1 : c = 1 := by
      have h := CFSG.Quasithin.eq_one_of_sq_eq_one_of_odd_card (H := Subgroup.center N) hZodd
        (g := (⟨c, hc⟩ : Subgroup.center N)) (by apply Subtype.ext; simpa using hc2)
      exact congrArg Subtype.val h
    have hconj : (MulAut.conjNormal (H := N) a) x = x := by rw [← hcx, hc1, one_mul]
    have hax : (a : G) * (x : G) = (x : G) * (a : G) := by
      simpa [MulAut.conjNormal_apply, mul_assoc] using
        congrArg (fun y : N => (y : G) * a) hconj
    exact hax.symm
  have hK : K = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact (Subgroup.closure_le K).mpr hmem
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have hnK : (⟨n, hn⟩ : N) ∈ K := by rw [hK]; trivial
  have hn' := Subgroup.mem_comap.mp hnK
  rwa [Subgroup.mem_centralizer_singleton_iff] at hn'

theorem ker_conjOnQuotient_comp_subtype [Finite G] {N : Subgroup G} [N.Normal]
    (hgen : Subgroup.closure {x : N | x ^ 2 = 1} = ⊤)
    (hZodd : Odd (Nat.card (Subgroup.center N))) (A : Subgroup G) :
    ((conjOnQuotient N).comp A.subtype).ker =
      (A ⊓ Subgroup.centralizer (N : Set G)).subgroupOf A := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro ha
    have ha' : ∀ n : N, (MulAut.conjNormal (H := N) (a : G)) n / n ∈ Subgroup.center N := by
      intro n
      have h := congrArg (fun f : MulAut (N ⧸ Subgroup.center N) => f (QuotientGroup.mk n)) ha
      change ((MulAut.mapQuotient (Subgroup.center N))
        (MulAut.conjNormal (H := N) (a : G))) (QuotientGroup.mk n) = QuotientGroup.mk n at h
      rw [MulAut.mapQuotient_mk] at h
      exact QuotientGroup.eq_iff_div_mem.mp h
    exact ⟨a.2, mem_centralizer_of_conjNormal_div_mem_center hgen hZodd ha'⟩
  · rintro ⟨-, haC⟩
    have hconj : MulAut.conjNormal (H := N) (a : G) = 1 := by
      ext n
      change (a : G) * (n : G) * (a : G)⁻¹ = (n : G)
      have hn : (n : G) * (a : G) = (a : G) * (n : G) :=
        Subgroup.mem_centralizer_iff.mp haC (n : G) n.2
      calc
        (a : G) * (n : G) * (a : G)⁻¹ = ((n : G) * (a : G)) * (a : G)⁻¹ := by rw [hn]
        _ = (n : G) := by group
    simp [conjOnQuotient, hconj]

theorem card_le_four_of_elemAbelian_mulAut_perm_five {L : Type*} [Group L]
    (e : L ≃* Equiv.Perm (Fin 5)) {I : Subgroup (MulAut L)}
    (hI2 : ∀ x ∈ I, x ^ 2 = 1) (hIc : ∀ x ∈ I, ∀ y ∈ I, x * y = y * x) :
    Nat.card I ≤ 4 := by
  let ψ : MulAut L ≃* MulAut (Equiv.Perm (Fin 5)) := MulAut.congr e
  let J : Subgroup (MulAut (Equiv.Perm (Fin 5))) := I.map ψ.toMonoidHom
  have hJcard : Nat.card J = Nat.card I := Subgroup.card_map_of_injective ψ.injective
  have hJ2 : ∀ x ∈ J, x ^ 2 = 1 := by
    rintro x ⟨y, hy, rfl⟩
    rw [← map_pow, hI2 y hy, map_one]
  have hJcomm : ∀ x ∈ J, ∀ y ∈ J, x * y = y * x := by
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hIc a ha b hb]
  let κ : Equiv.Perm (Fin 5) ≃* MulAut (Equiv.Perm (Fin 5)) :=
    MulEquiv.ofBijective MulAut.conj CFSG.Monster.B.TwoA.sym5_conj_bijective
  let E : Subgroup (Equiv.Perm (Fin 5)) := J.map κ.symm.toMonoidHom
  have hEcard : Nat.card E = Nat.card J :=
    Subgroup.card_map_of_injective κ.symm.injective
  have hE2 : ∀ x ∈ E, x * x = 1 := by
    rintro x ⟨y, hy, rfl⟩
    have hy2 : y * y = 1 := by
      have := hJ2 y hy
      rwa [pow_two] at this
    rw [← map_mul, hy2, map_one]
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hJcomm a ha b hb]
  have hE4 : Nat.card E ≤ 4 :=
    CFSG.Quasithin.card_le_four_of_elemAbelian_perm_five E hEcomm hE2
  rw [← hJcard, ← hEcard]
  exact hE4

theorem card_range_conjOnQuotient_comp_subtype_le_four [Finite G] {N : Subgroup G} [N.Normal]
    (e : N ⧸ Subgroup.center N ≃* Equiv.Perm (Fin 5)) {A : Subgroup G}
    (hA2 : ∀ x ∈ A, x ^ 2 = 1) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    Nat.card ((conjOnQuotient N).comp A.subtype).range ≤ 4 := by
  classical
  have h2 : ∀ x ∈ ((conjOnQuotient N).comp A.subtype).range, x ^ 2 = 1 := by
    rintro x ⟨a, rfl⟩
    have ha2 : a ^ 2 = 1 := Subtype.ext (hA2 (a : G) a.2)
    rw [← map_pow, ha2, map_one]
  have hcomm : ∀ x ∈ ((conjOnQuotient N).comp A.subtype).range,
      ∀ y ∈ ((conjOnQuotient N).comp A.subtype).range, x * y = y * x := by
    rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩
    have hab : a * b = b * a := Subtype.ext (hAc (a : G) a.2 (b : G) b.2)
    rw [← map_mul, ← map_mul, hab]
  exact card_le_four_of_elemAbelian_mulAut_perm_five e h2 hcomm

theorem card_le_four_mul_card_inf_centralizer_of_perm_five [Finite G]
    {N : Subgroup G} [N.Normal]
    (hgen : Subgroup.closure {x : N | x ^ 2 = 1} = ⊤)
    (hZodd : Odd (Nat.card (Subgroup.center N)))
    (e : N ⧸ Subgroup.center N ≃* Equiv.Perm (Fin 5))
    {A : Subgroup G} (hA2 : ∀ x ∈ A, x ^ 2 = 1)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    Nat.card A ≤ 4 * Nat.card ↥(A ⊓ Subgroup.centralizer (N : Set G)) := by
  let ρ : A →* MulAut (N ⧸ Subgroup.center N) := (conjOnQuotient N).comp A.subtype
  have hker : ρ.ker = (A ⊓ Subgroup.centralizer (N : Set G)).subgroupOf A :=
    ker_conjOnQuotient_comp_subtype hgen hZodd A
  have hcard := Subgroup.card_ker_mul_card_range ρ
  rw [hker] at hcard
  have hcardker : Nat.card ↥((A ⊓ Subgroup.centralizer (N : Set G)).subgroupOf A) =
      Nat.card ↥(A ⊓ Subgroup.centralizer (N : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hcardker] at hcard
  have hrange := card_range_conjOnQuotient_comp_subtype_le_four e hA2 hAc
  calc
    Nat.card A = Nat.card ↥(A ⊓ Subgroup.centralizer (N : Set G)) * Nat.card ρ.range :=
      hcard.symm
    _ ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (N : Set G)) * 4 := Nat.mul_le_mul_left _ hrange
    _ = 4 * Nat.card ↥(A ⊓ Subgroup.centralizer (N : Set G)) := by ring

end CFSG.GroupTheory
