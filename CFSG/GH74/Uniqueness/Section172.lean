module

public import CFSG.GH74.Uniqueness.Section172Frat
public import CFSG.GH74.Uniqueness.Section172Arith
public import CFSG.GH74.Uniqueness.Section172aB
public import CFSG.GH74.Uniqueness.Section172P
public import CFSG.GH74.Uniqueness.Section172Omega

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.lemma172b (S : ZDSetup X Z M) (h164 : Lemma164Stmt Z M) (h166 : Cor166Stmt Z M)
    (h171 : Lemma171Stmt Z M) (haB : Lemma172aBStmt Z M) (hP : Lemma172PStmt Z M)
    (c : Conf16 Z M) (n i e : ℕ) (hB : BenderSub Z M (cenHull Z c.u) n i e) :
    (c.D ⊓ centralizer ({c.t, c.u} : Set X)).relIndex
        (c.D ⊓ centralizer ({c.t * c.u} : Set X)) ≡ 1 [MOD 2 ^ n] := by
  have ha := S.lemma172a haB c n i e hB
  have hCu : c.D ⊓ centralizer ({c.t, c.u} : Set X) ≤ c.D ⊓ centralizer ({c.u} : Set X) :=
    inf_le_inf_left _ (fun x hx => (mem_centralizer_pair_iff.mp hx).2)
  have hCtu : c.D ⊓ centralizer ({c.t, c.u} : Set X) ≤ c.D ⊓ centralizer ({c.t * c.u} : Set X) := by
    refine inf_le_inf_left _ (fun x hx => ?_)
    obtain ⟨hxt, hxu⟩ := mem_centralizer_pair_iff.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hxt hxu ⊢
    calc x * (c.t * c.u) = (x * c.t) * c.u := by rw [mul_assoc]
      _ = (c.t * x) * c.u := by rw [hxt]
      _ = c.t * (x * c.u) := by rw [mul_assoc]
      _ = c.t * (c.u * x) := by rw [hxu]
      _ = (c.t * c.u) * x := by rw [mul_assoc]
  have hA := Subgroup.relIndex_mul_card (c.D ⊓ centralizer ({c.t, c.u} : Set X))
    (c.D ⊓ centralizer ({c.u} : Set X))
  have hB' := Subgroup.relIndex_mul_card (c.D ⊓ centralizer ({c.t, c.u} : Set X))
    (c.D ⊓ centralizer ({c.t * c.u} : Set X))
  rw [inf_eq_left.mpr hCu] at hA
  rw [inf_eq_left.mpr hCtu] at hB'
  rw [ha] at hA
  obtain ⟨hr, h171'⟩ := h171 c n i e hB
  have hdiv : 2 ^ n * Nat.card ↥c.P ∣ (omega M).ncard - 1 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨-, -, ⟨hconj, -⟩, -, he⟩ := h166 c
    obtain ⟨-, hcyc⟩ := he c.D (S.zHull_dGrp_eq_bot c.htM)
    let u' : ↥c.D := ⟨c.u, c.hu⟩
    have hu'2 : orderOf u' = 2 := by rw [← Subgroup.orderOf_coe]; exact c.hu2
    obtain ⟨Q₂, hQ₂⟩ := IsPGroup.exists_le_sylow
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu'2, pow_one]) :
        IsPGroup 2 (Subgroup.zpowers u'))
    refine (h164 c n i e hB).2.2 ⟨(Q₂ : Subgroup ↥c.D).map c.D.subtype, ⟨Q₂, rfl⟩,
      ⟨u', hQ₂ (Subgroup.mem_zpowers u'), rfl⟩, ?_⟩ hconj
    intro y hy
    obtain ⟨y', hy', rfl⟩ := hy
    have hcomm : y' * u' = u' * y' := by
      have := hcyc Q₂
      let _ : CommGroup ↥(Q₂ : Subgroup ↥c.D) := IsCyclic.commGroup
      exact congrArg Subtype.val (mul_comm (⟨y', hy'⟩ : ↥(Q₂ : Subgroup ↥c.D))
        ⟨u', hQ₂ (Subgroup.mem_zpowers u')⟩)
    exact congrArg (fun a : ↥c.D => (a : X)) hcomm
  rw [hP c n i e hB] at hdiv
  have hn2 : 2 ≤ n := hB.bender.two_le.2
  have hq : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hi1 : i ≠ 0 := by
    have := hB.bender.two_le.1
    omega
  exact arith_172b hq (dvd_pow_self _ hi1) (pow_pos (pow_pos (by norm_num) n) i) Nat.card_pos hA.symm
    hB'.symm h171' hr hdiv

theorem ZDSetup.lemma172_of
    (S : ZDSetup X Z M) (h121 : Thm121Stmt Z M) (h161 : Lemma161Stmt Z M)
    (h164 : Lemma164Stmt Z M) (h166 : Cor166Stmt Z M) (h167 : Lemma167Stmt Z M)
    (h171 : Lemma171Stmt Z M) (haB : Lemma172aBStmt Z M) (hP : Lemma172PStmt Z M) :
    Lemma172Stmt Z M := by
  intro c n i e hB
  obtain ⟨hc, hd, he, hf⟩ := S.lemma172_cdef h121 h161 h164 h166 h167 c hB
  exact ⟨S.lemma172a haB c n i e hB, S.lemma172b h164 h166 h171 haB hP c n i e hB, hc, hd, he, hf⟩

theorem ZDSetup.lemma172
    (S : ZDSetup X Z M) (h121 : Thm121Stmt Z M) (h161 : Lemma161Stmt Z M)
    (h164 : Lemma164Stmt Z M) (h166 : Cor166Stmt Z M) (h167 : Lemma167Stmt Z M)
    (h171 : Lemma171Stmt Z M) : Lemma172Stmt Z M :=
  S.lemma172_of h121 h161 h164 h166 h167 h171 S.lemma172aB S.lemma172P

end CFSG.GH74.Uniqueness
