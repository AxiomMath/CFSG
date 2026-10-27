module

public import CFSG.ClassicalInvolution.Sp62Rec.PkgNoHat
import CFSG.ClassicalInvolution.Sp62Rec.Balance
import CFSG.GroupTheory.CyclicSylowNormalOddComplement

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance CFSG.Open

variable {G : Type} [Group G] [Finite G] {z e : G}
  {E B : Subgroup G}

theorem I1Six.centralizer_eq_zpowers_of_Z5b (P : I1Six z e E B)
    (hodd : oddCoreIn (Subgroup.centralizer ({e} : Set G)) = ⊥)
    (he2 : e * e = 1) (he1 : e ≠ 1)
    (hQ2 : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Subgroup.centralizer (E : Set G) →
      Nat.card ↥Q ≤ 2) :
    Subgroup.centralizer (E : Set G) = Subgroup.zpowers e := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Ce, hCe⟩ : ∃ C : Subgroup G, C = Subgroup.centralizer ({e} : Set G) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ C : Subgroup G, C = Subgroup.centralizer (E : Set G) := ⟨_, rfl⟩
  rw [← hCe] at hodd
  have hCemem : ∀ x, x ∈ Ce ↔ x * e = e * x := fun x => by
    rw [hCe]
    exact Subgroup.mem_centralizer_singleton_iff
  have hYmem : ∀ x, x ∈ Y ↔ ∀ h ∈ E, h * x = x * h := fun x => by
    rw [hY]
    exact Subgroup.mem_centralizer_iff
  have hEB : E ≤ B := P.E_le_B
  have hBC : B ≤ Ce := by
    rw [hCe]
    exact P.B_le
  have hEC : E ≤ Ce := hEB.trans hBC
  have heE : e ∈ E := P.e_mem
  have hEc : ∀ g ∈ Ce, ∀ x ∈ E, g * x * g⁻¹ ∈ E := by
    intro g hg x hx
    have hgC : g ∈ Subgroup.centralizer ({e} : Set G) := by
      rw [← hCe]
      exact hg
    have h1 := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx
    rw [P.E_normal g hgC] at h1
    exact h1
  have hYCe : Y ≤ Ce := by
    intro g hg
    rw [hYmem] at hg
    exact (hCemem g).mpr (hg e heE).symm
  have hY_e : e ∈ Y := by
    rw [hYmem]
    intro h hh
    exact (hCemem h).mp (hEC hh)
  have hYconj : ∀ g ∈ Ce, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
    intro g hg y hy
    rw [hYmem]
    intro x hx
    have hx' : g⁻¹ * x * g ∈ E := by
      have := hEc g⁻¹ (Ce.inv_mem hg) x hx
      rwa [inv_inv] at this
    have hxy : (g⁻¹ * x * g) * y = y * (g⁻¹ * x * g) := (hYmem y).mp hy _ hx'
    calc x * (g * y * g⁻¹) = g * ((g⁻¹ * x * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by rw [hxy]
      _ = g * y * g⁻¹ * x := by group
  have hCeN : Ce ≤ Subgroup.normalizer (Y : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hYconj g hg y
    · intro hy
      have := hYconj g⁻¹ (Ce.inv_mem hg) _ hy
      simpa [mul_assoc] using this
  have hoddY : oddCoreIn Y = ⊥ := by
    have hsub : IsSubnormal Y Ce :=
      isSubnormal_of_normal_subgroupOf hYCe
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hYCe).mpr hCeN)
    have h1 := oddCoreIn_le_of_isSubnormal hsub
    rw [hodd] at h1
    exact le_bot_iff.mp h1
  have hQ2y : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Y → Nat.card ↥Q ≤ 2 := by
    intro Q hQ hQY
    exact hQ2 Q hQ (by rw [← hY]; exact hQY)
  have hYcard : Nat.card ↥Y ≤ 2 := by
    obtain ⟨S⟩ : Nonempty (Sylow 2 ↥Y) := inferInstance
    have hSle : Nat.card S ≤ 2 := by
      have hQ2' : IsPGroup 2 ((S : Subgroup ↥Y).map Y.subtype) :=
        S.isPGroup'.map Y.subtype
      have hle := hQ2y _ hQ2' (Subgroup.map_subtype_le _)
      rwa [Subgroup.card_map_of_injective Y.subtype_injective] at hle
    have hcyc : IsCyclic S := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
      rcases n with _ | _ | n
      · have h1 : Nat.card S = 1 := by simpa using hn
        haveI : Subsingleton S := (Nat.card_eq_one_iff_unique.mp h1).1
        exact isCyclic_of_subsingleton
      · have h2 : Nat.card S = 2 := by simpa using hn
        exact isCyclic_of_prime_card (p := 2) h2
      · exfalso
        have h4 : 4 ≤ Nat.card S := by
          rw [hn, pow_succ, pow_succ]
          have := pow_pos (by norm_num : (0 : ℕ) < 2) n
          omega
        omega
    have hcomp := CFSG.cyclic_sylow_normal_odd_complement S hcyc
    have hidx := hcomp.2.2.2.1.2.2.1
    have hpp : CFSG.pPrimeCore 2 ↥Y = ⊥ := (oddCoreIn_eq_bot_iff Y).mp hoddY
    rw [hpp, Subgroup.index_bot] at hidx
    rw [hidx]
    exact hSle
  have hzp : Nat.card ↥(Subgroup.zpowers e) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (p := 2) (by rw [sq]; exact he2) he1]
  have hle : Subgroup.zpowers e ≤ Y := Subgroup.zpowers_le.mpr hY_e
  rw [← hY]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hzp]; exact hYcard)).symm

end CFSG.ClassicalInvolution.Sp62Rec
