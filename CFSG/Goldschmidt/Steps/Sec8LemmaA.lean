module

import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.Goldschmidt.Steps.Fusion
import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.BasicG

public section

namespace CFSG.Goldschmidt

open CFSG.Open

namespace Sec8

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

theorem mem_normalizer_of_conjSub_le (hset : GoldSetting G S A) {g : G}
    (hg : conjSub g A ≤ S) : g ∈ Subgroup.normalizer (A : Set G) := by
  have heq := conj_eq_of_conj_le hset.closed hg
  refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
  rw [← mem_conjSub, heq]

omit [Finite G] in
theorem fusionIsSylowIn_of_le {N : Subgroup G} (hSN : (S : Subgroup G) ≤ N) :
    fusionIsSylowIn 2 (S : Subgroup G) N :=
  ⟨hSN, S.isPGroup', fun _ _ hP hSP => S.is_maximal' hP hSP⟩

theorem exists_conj_normalizer (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {N : Subgroup G}
    (hSN : (S : Subgroup G) ≤ N) {b g : G} (hb : b ∈ A) (hg : g ∈ N) (hgb : g⁻¹ * b * g ∈ A) :
    ∃ n ∈ N, n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) ∧
      n⁻¹ * b * n = g⁻¹ * b * g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c := g⁻¹ * b * g with hc
  set K := N ⊓ Subgroup.centralizer ({c} : Set G) with hK
  have hSK : (S : Subgroup G) ≤ K := le_inf hSN (le_centralizer_singleton hset h4 hgb)
  have hS'K : Quasithin.conjSubgroup (S : Subgroup G) g ≤ K := by
    intro x hx
    rw [Quasithin.mem_conjSubgroup_iff] at hx
    refine ⟨?_, ?_⟩
    · have := N.mul_mem (N.mul_mem (N.inv_mem hg) (hSN hx)) hg
      simpa [mul_assoc] using this
    · show x ∈ Subgroup.centralizer ({c} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxb := Subgroup.mem_centralizer_singleton_iff.mp
        (le_centralizer_singleton hset h4 hb hx)
      calc x * c = g⁻¹ * ((g * x * g⁻¹) * b) * g := by rw [hc]; group
        _ = g⁻¹ * (b * (g * x * g⁻¹)) * g := by rw [hxb]
        _ = c * x := by rw [hc]; group
  obtain ⟨d, hdK, y, hy1, hy2⟩ := Quasithin.exists_conj_le_sylow_of_isPGroup S hSK hS'K
    S.isPGroup' (S.isPGroup'.map _)
  have hcard : ∀ {z : G}, Quasithin.conjSubgroup (S : Subgroup G) z ≤ S →
      z ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) := fun {z} hz => by
    have heq : Quasithin.conjSubgroup (S : Subgroup G) z = S :=
      Subgroup.eq_of_le_of_card_ge hz (by
        rw [Quasithin.conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj z⁻¹).injective])
    exact Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp heq
  have hyN := hcard hy1
  rw [Quasithin.conjSubgroup_conjSubgroup] at hy2
  have hgdy := hcard hy2
  refine ⟨g * d, N.mul_mem hg hdK.1, ?_, ?_⟩
  · have := Subgroup.mul_mem _ hgdy (Subgroup.inv_mem _ hyN)
    simpa [mul_assoc] using this
  · have hdc := Subgroup.mem_centralizer_singleton_iff.mp hdK.2
    calc (g * d)⁻¹ * b * (g * d) = d⁻¹ * c * d := by rw [hc]; group
      _ = c := by rw [mul_assoc, ← hdc, ← mul_assoc, inv_mul_cancel, one_mul]

omit [Finite G] in
theorem le_normalizer_sup_oddCoreOf {N : Subgroup G}
    (hz : ∀ b ∈ A, ∀ g ∈ N, g * b * g⁻¹ * b⁻¹ ∈ oddCoreOf N) :
    N ≤ Subgroup.normalizer ((A ⊔ oddCoreOf N : Subgroup G) : Set G) := by
  have hmap : ∀ g ∈ N, (A ⊔ oddCoreOf N).map (MulAut.conj g).toMonoidHom ≤ A ⊔ oddCoreOf N := by
    intro g hg
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨b, hb, rfl⟩
      have : (MulAut.conj g).toMonoidHom b = (g * b * g⁻¹ * b⁻¹) * b := by
        simp [MulAut.conj_apply]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hz b hb g hg)) (Subgroup.mem_sup_left hb)
    · rintro _ ⟨y, hy, rfl⟩
      exact Subgroup.mem_sup_right
        ((Subgroup.mem_normalizer_iff.mp (le_normalizer_oddCoreOf N hg) y).mp hy)
  intro g hg
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => hmap g hg ⟨x, hx, rfl⟩, fun hx => ?_⟩
  have := hmap g⁻¹ (N.inv_mem hg) ⟨_, hx, rfl⟩
  simpa [MulAut.conj_apply, mul_assoc] using this

end Sec8

open Sec8 in
theorem GLemmaA :
    ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), GoldSetting G S A →
      Nat.card A = 4 → ∀ N : Subgroup G, N ≠ ⊤ → (S : Subgroup G) ≤ N →
      N ⊓ Subgroup.normalizer (A : Set G) = Subgroup.centralizer (A : Set G) →
      normalClosureIn N A = oddCoreOf (normalClosureIn N A) ⊔ A ∧
        N = oddCoreOf (normalClosureIn N A) ⊔ Subgroup.centralizer (A : Set G) := by
  intro G _ _ S A hset h4 N _ hSN hNA
  have hAN : A ≤ N := hset.le.trans hSN
  have hiso : ∀ b ∈ A, ∀ g ∈ N, g⁻¹ * b * g ∈ (S : Subgroup G) → g⁻¹ * b * g = b := by
    intro b hb g hg hgS
    obtain ⟨n, hnN, hnS, hn⟩ :=
      exists_conj_normalizer hset h4 hSN hb hg (hset.closed b hb g hgS)
    have hnA := N3a G S A S hset.le hset.closed S.isPGroup' hset.le hnS
    have hnC : n ∈ Subgroup.centralizer (A : Set G) := hNA ▸ ⟨hnN, hnA⟩
    rw [← hn]
    simpa using conj_eq_of_mem_centralizer (Subgroup.inv_mem _ hnC) hb
  have hz : ∀ b ∈ A, ∀ g ∈ N, g * b * g⁻¹ * b⁻¹ ∈ oddCoreOf N := by
    intro b hb g hg
    by_cases hb1 : b = 1
    · rw [hb1]
      simp
    exact commutator_mem_oddCoreOf (fusionIsSylowIn_of_le hSN) (hset.le hb)
      (le_centralizer_singleton hset h4 hb) (mul_self_eq_one hset.elem hb) hb1
      (hiso b hb) hg
  set Q := normalClosureIn N A with hQdef
  have hQN : Q ≤ N := normalClosureIn_le_self N A
  have hAQ : A ≤ Q := le_normalClosureIn hAN
  have hQle : Q ≤ A ⊔ oddCoreOf N :=
    normalClosureIn_le (sup_le hAN (oddCoreOf_le N)) (le_normalizer_sup_oddCoreOf hz)
      (inf_le_left.trans le_sup_left)
  have hQeq : Q = oddCoreOf Q ⊔ A := by
    refine le_antisymm (fun q hq => ?_) (sup_le (oddCoreOf_le Q) hAQ)
    have hq' := hQle hq
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A (oddCoreOf N)
      (hAN.trans (le_normalizer_oddCoreOf N))] at hq'
    obtain ⟨b, hb, y, hy, rfl⟩ := Set.mem_mul.mp hq'
    have hyQ : y ∈ Q := by simpa using Q.mul_mem (Q.inv_mem (hAQ hb)) hq
    have hyO : y ∈ oddCoreOf Q := by
      refine le_oddCoreOf (N := Q ⊓ oddCoreOf N) inf_le_left (fun q hq => ?_) ?_ ⟨hyQ, hy⟩
      · exact mem_normalizer_inf (Subgroup.le_normalizer hq)
          (le_normalizer_oddCoreOf N (hQN hq))
      · exact (odd_card_oddCoreOf N).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hb) (Subgroup.mem_sup_left hyO)
  refine ⟨hQeq, le_antisymm (fun n hn => ?_)
    (sup_le ((oddCoreOf_le Q).trans hQN) (hNA ▸ inf_le_left))⟩
  have hA2 : IsPGroup 2 A := S.isPGroup'.to_le hset.le
  have hAnQ : Quasithin.conjSubgroup A n ≤ Q := by
    intro x hx
    rw [Quasithin.mem_conjSubgroup_iff] at hx
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_normalClosureIn N A
      (N.inv_mem hn)) _).mp (hAQ hx)
    simpa [mul_assoc] using this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcQ, y, hy1, hy2⟩ :=
    Quasithin.exists_conj_le_sylow_of_isPGroup S hAQ hAnQ hA2 (hA2.map _)
  have hyN : y ∈ Subgroup.normalizer (A : Set G) := mem_normalizer_of_conjSub_le hset hy1
  rw [Quasithin.conjSubgroup_conjSubgroup] at hy2
  have hncy : n * (c * y) ∈ Subgroup.normalizer (A : Set G) :=
    mem_normalizer_of_conjSub_le hset hy2
  have hncN : n * c ∈ Subgroup.normalizer (A : Set G) := by
    have := Subgroup.mul_mem _ hncy (Subgroup.inv_mem _ hyN)
    simpa [mul_assoc] using this
  have hnc : n * c ∈ N ⊓ Subgroup.normalizer (A : Set G) := ⟨N.mul_mem hn (hQN hcQ), hncN⟩
  rw [hNA] at hnc
  have hc' : c⁻¹ ∈ oddCoreOf Q ⊔ A := hQeq ▸ Q.inv_mem hcQ
  have hAC : A ≤ Subgroup.centralizer (A : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => comm hset.elem hb ha
  have hn' : n = n * c * c⁻¹ := by group
  rw [hn']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hnc) ((sup_le_sup_left hAC _) hc')

end CFSG.Goldschmidt
