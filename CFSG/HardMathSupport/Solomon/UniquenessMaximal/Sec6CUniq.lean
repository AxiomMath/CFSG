module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6CUniqAux1
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6CUniqAux2
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6CUniqAux3
public import CFSG.LocalAnalysis.GLTheoremB.Lemma23Proof

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6C

variable {G : Type} [Group G] [Finite G]

theorem uniqComp_of_B1max (hS : GLStanding G 4 3) {B : Subgroup G} (hB : IsBOneMax 3 B) :
    UniqComp B := by
  intro x hxB hx1 I K hI hK hBI hBK hIl hKl hF
  by_contra hne
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSC : IsSCp 3 ⊤ B := lemma23_proved G 4 3 hS B hB
  have hBel : IsElemAbelian 3 B := hB.1.1
  have hBcard : Nat.card B = 81 := by
    have := hS.card_eq hB
    norm_num at this
    exact this
  have hB3 : IsPGroup 3 B := fun g =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hBel.2 g g.2)⟩
  have hcommB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb => elemAbelian_comm hBel ha hb
  have hxK : x ∉ K := by
    intro hxK
    have hx' : x ∈ GLAPPrimeCoreOf 3 K := by
      refine mem_glaPPrimeCoreOf_of_commutator_mem hKl hxK fun g hg => ?_
      have h1 : x * g = g * x := Subgroup.mem_centralizer_iff.1 (hK.1 hg) x rfl
      have h2 : g * x * g⁻¹ * x⁻¹ = 1 := by
        rw [← h1]
        group
      rw [h2]
      exact one_mem _
    exact hx1 (eq_one_of_pow_three_mem_glaPPrimeCoreOf hx' (hBel.2 x hxB))
  have hQ : I ⊓ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G)) = GLAPPrimeCoreOf 3 I :=
    glaPPrimeCoreOf_inf_eq_of_isSubnormal Nat.prime_three hI.2.1
  have hIF : ∀ f ∈ B ⊓ K, ∀ g ∈ I, f * g * f⁻¹ * g⁻¹ ∈ GLAPPrimeCoreOf 3 I := by
    intro f hf g hg
    have h1 := commutator_mem_glaPPrimeCoreOf_of_ne hI hK hne hg hf.2
    have h2 : f * g * f⁻¹ * g⁻¹ ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G)) := by
      have := inv_mem h1
      simpa [mul_assoc] using this
    have h3 : f * g * f⁻¹ * g⁻¹ ∈ I :=
      I.mul_mem ((Subgroup.mem_normalizer_iff.1 (hBI hf.1) g).1 hg) (I.inv_mem hg)
    rw [← hQ]
    exact ⟨h3, h2⟩
  have hxF : Subgroup.zpowers x ≤ Subgroup.centralizer ((B ⊓ K : Subgroup G) : Set G) := by
    rintro _ ⟨m, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact ((Commute.zpow_right (show Commute f x from hcommB f hf.1 x hxB) m)).eq
  set A : Subgroup G := Subgroup.zpowers x ⊔ (B ⊓ K) with hAdef
  have hAB : A ≤ B := sup_le (Subgroup.zpowers_le.2 hxB) inf_le_left
  have hA3 : IsPGroup 3 A := hB3.to_le hAB
  have hAcomm : ∀ a ∈ A, ∀ g ∈ I, a * g * a⁻¹ * g⁻¹ ∈ GLAPPrimeCoreOf 3 I := by
    intro a ha g hg
    obtain ⟨u, hu, f, hf, rfl⟩ := exists_mul_of_mem_sup hxF ha
    have hux : ∀ y ∈ Subgroup.centralizer ({x} : Set G), u * y * u⁻¹ = y := by
      obtain ⟨m, rfl⟩ := hu
      intro y hy
      have hxy : Commute x y := Subgroup.mem_centralizer_iff.1 hy x rfl
      rw [mul_inv_eq_iff_eq_mul]
      exact (Commute.zpow_left hxy m).eq
    have hfg : f * g * f⁻¹ ∈ I := (Subgroup.mem_normalizer_iff.1 (hBI hf.1) g).1 hg
    have e : u * f * g * (u * f)⁻¹ * g⁻¹ = (u * (f * g * f⁻¹) * u⁻¹) * g⁻¹ := by group
    rw [e, hux _ (hI.1 hfg)]
    exact hIF f hf g hg
  have hAI : ∀ a ∈ A, a ∈ I → a = 1 := by
    intro a haA haI
    have ha' : a ∈ GLAPPrimeCoreOf 3 I := by
      refine mem_glaPPrimeCoreOf_of_commutator_mem hIl haI fun g hg => ?_
      have := inv_mem (hAcomm a haA g hg)
      simpa [mul_assoc] using this
    exact eq_one_of_pow_three_mem_glaPPrimeCoreOf ha' (hBel.2 a (hAB haA))
  set H : Subgroup G := I ⊓ Subgroup.centralizer (A : Set G) with hHdef
  have h9 : 9 ∣ Nat.card H :=
    nine_dvd_card_inf_centralizer hIl hA3 (fun a ha => hBI (hAB ha)) hAcomm
  have hBH : B ≤ Subgroup.normalizer (H : Set G) := by
    intro b hb
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hBI hb) n).1 hn.1, ?_⟩
    show b * n * b⁻¹ ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hn' : a * n = n * a := Subgroup.mem_centralizer_iff.1 hn.2 a ha
    have hba : a * b = b * a := hcommB a (hAB ha) b hb
    have hab' : a * b⁻¹ = b⁻¹ * a := (show Commute a b from hba).inv_right.eq
    calc a * (b * n * b⁻¹) = (a * b) * n * b⁻¹ := by group
      _ = (b * a) * n * b⁻¹ := by rw [hba]
      _ = b * (a * n) * b⁻¹ := by group
      _ = b * (n * a) * b⁻¹ := by rw [hn']
      _ = b * n * (a * b⁻¹) := by group
      _ = b * n * (b⁻¹ * a) := by rw [hab']
      _ = (b * n * b⁻¹) * a := by group
  obtain ⟨S, hSH, hS3, hSord, hBS⟩ :=
    exists_sylow_normalized_of_isPGroup (p := 3) H B hB3 hBH
  have hSI : S ≤ I := hSH.trans inf_le_left
  have h9S : 9 ∣ Nat.card S := by
    have := hSord 2 (by simpa using h9)
    simpa using this
  obtain ⟨hSle, hSel⟩ := card_le_nine_of_isPGroup hSI hS3 hIl
  have hS9 : Nat.card S = 9 := le_antisymm hSle (Nat.le_of_dvd Nat.card_pos h9S)
  have hSel' := hSel hS9
  have hSbot : S ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hS9
    omega
  obtain ⟨w, hwS, hw1, hwcomm⟩ :=
    exists_ne_one_mem_centralizer_of_isPGroup S B hS3 hSbot hB3 hBS
  have hw3 : w ^ 3 = 1 := hSel'.2 w hwS
  have hwB : w ∈ B := by
    refine mem_of_pow_eq_one_of_isSCp hSC ?_ hw3
    rw [Subgroup.mem_centralizer_iff]
    exact fun h hh => hwcomm h hh
  have hwA : w ∉ A := fun h => hw1 (hAI w h (hSI hwS))
  have hFcard : Nat.card (B ⊓ K : Subgroup G) = 9 := by
    have := hF.2.2
    simpa using this
  have hFA : (B ⊓ K : Subgroup G) < A := by
    refine lt_of_le_of_ne le_sup_right fun h => hxK ?_
    have hxA : x ∈ A := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
    rw [← h] at hxA
    exact hxA.2
  have hdiv81 : ∀ d : ℕ, d ∣ 81 → d = 1 ∨ d = 3 ∨ d = 9 ∨ d = 27 ∨ d = 81 := by
    intro d hd
    have hmem : d ∈ Nat.divisors 81 := Nat.mem_divisors.2 ⟨hd, by norm_num⟩
    have : Nat.divisors 81 = {1, 3, 9, 27, 81} := by decide
    rw [this] at hmem
    simpa using hmem
  have h9A : 9 ∣ Nat.card A := hFcard ▸ Subgroup.card_dvd_of_le le_sup_right
  have hA81 : Nat.card A ∣ 81 := hBcard ▸ Subgroup.card_dvd_of_le hAB
  have hgtA : 9 < Nat.card A := hFcard ▸ card_lt_of_lt' hFA
  have h27 : 27 ≤ Nat.card A := by
    rcases hdiv81 _ hA81 with h | h | h | h | h <;> omega
  have hE₁B : A ⊔ Subgroup.zpowers w ≤ B := sup_le hAB (Subgroup.zpowers_le.2 hwB)
  have hAE : A < A ⊔ Subgroup.zpowers w := by
    refine lt_of_le_of_ne le_sup_left fun h => hwA ?_
    have : w ∈ A ⊔ Subgroup.zpowers w := Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
    rwa [← h] at this
  have hE₁81 : Nat.card (A ⊔ Subgroup.zpowers w : Subgroup G) = 81 := by
    have h1 := card_lt_of_lt' hAE
    have h2 : Nat.card (A ⊔ Subgroup.zpowers w : Subgroup G) ∣ 81 :=
      hBcard ▸ Subgroup.card_dvd_of_le hE₁B
    rcases hdiv81 _ h2 with h | h | h | h | h <;> omega
  have hBE : A ⊔ Subgroup.zpowers w = B :=
    Subgroup.eq_of_le_of_card_ge hE₁B (by rw [hBcard, hE₁81])
  have hAcw : A ≤ Subgroup.centralizer ((Subgroup.zpowers w : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨m, rfl⟩
    exact (Commute.zpow_left (show Commute w a from hcommB w hwB a (hAB ha)) m).eq
  have hwzS : Subgroup.zpowers w ≤ S := Subgroup.zpowers_le.2 hwS
  have hSB : ∀ s ∈ S, ∀ b ∈ B, b * s = s * b := by
    intro s hs b hb
    rw [← hBE] at hb
    obtain ⟨a, ha, u, hu, rfl⟩ := exists_mul_of_mem_sup hAcw hb
    have h1 : a * s = s * a := Subgroup.mem_centralizer_iff.1 (hSH hs).2 a ha
    have h2 : u * s = s * u := elemAbelian_comm hSel' (hwzS hu) hs
    calc a * u * s = a * (u * s) := by group
      _ = a * (s * u) := by rw [h2]
      _ = (a * s) * u := by group
      _ = (s * a) * u := by rw [h1]
      _ = s * (a * u) := by group
  have hzcard : Nat.card (Subgroup.zpowers w) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hw3 hw1
  have hnle : ¬ S ≤ Subgroup.zpowers w := fun h => by
    have := Subgroup.card_le_of_le h
    omega
  obtain ⟨s, hsS, hsw⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
  have hs3 : s ^ 3 = 1 := hSel'.2 s hsS
  have hsB : s ∈ B := by
    refine mem_of_pow_eq_one_of_isSCp hSC ?_ hs3
    rw [Subgroup.mem_centralizer_iff]
    exact fun b hb => hSB s hsS b hb
  rw [← hBE] at hsB
  obtain ⟨a, ha, u, hu, hsau⟩ := exists_mul_of_mem_sup hAcw hsB
  have haI : a ∈ I := by
    have h1 : a = s * u⁻¹ := by rw [hsau]; group
    rw [h1]
    exact I.mul_mem (hSI hsS) (I.inv_mem (hSI (hwzS hu)))
  have ha1 := hAI a ha haI
  apply hsw
  rw [hsau, ha1, one_mul]
  exact hu

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
