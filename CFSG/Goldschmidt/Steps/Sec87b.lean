module

import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec84b
import CFSG.Goldschmidt.Steps.Sec85a
import CFSG.Goldschmidt.Steps.Sec87a
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.BasicG

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

theorem exists_omega1 {p : ℕ} (hp : p.Prime) {P : Subgroup G}
    (hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hrank : CFSG.Open.pRank p P = 2) :
    ∃ V : Subgroup G, V ≤ P ∧ IsMulCommutative V ∧ (∀ v ∈ V, v ^ p = 1) ∧
      Nat.card V = p ^ 2 ∧ ∀ y ∈ P, y ^ p = 1 → y ∈ V := by
  have : Fact p.Prime := ⟨hp⟩
  let V : Subgroup G :=
    { carrier := {y | y ∈ P ∧ y ^ p = 1}
      mul_mem' := fun {x y} hx hy => ⟨P.mul_mem hx.1 hy.1, by
        rw [(Commute.mul_pow (hPab x hx.1 y hy.1)), hx.2, hy.2, one_mul]⟩
      one_mem' := ⟨P.one_mem, one_pow p⟩
      inv_mem' := fun {x} hx => ⟨P.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hVP : V ≤ P := fun y hy => hy.1
  have hVab : IsMulCommutative V := ⟨⟨fun x y => Subtype.ext (hPab _ (hVP x.2) _ (hVP y.2))⟩⟩
  have hVp : ∀ v ∈ V, v ^ p = 1 := fun v hv => hv.2
  have hVpg : IsPGroup p V := fun v => ⟨1, Subtype.ext (by simpa using hVp _ v.2)⟩
  obtain ⟨k, hk⟩ := hVpg.exists_card_eq
  have hk2 : k ≤ 2 := hrank ▸ CFSG.SectionRank.le_pRank hp.one_lt hVP ⟨hVab, hVp⟩ hk
  obtain ⟨E, hEP, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt P
  have hEV : E ≤ V := fun y hy => ⟨hEP hy, hE.2 y hy⟩
  have hdvd := Subgroup.card_dvd_of_le hEV
  rw [hEc, hk, hrank] at hdvd
  have hk2' : 2 ≤ k := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
  exact ⟨V, hVP, hVab, hVp, by rw [hk, show k = 2 by omega], fun y hy hy1 => ⟨hy, hy1⟩⟩

omit [Finite G] in
theorem mem_centralizer_of_forall_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P V : Subgroup G}
    (hPp : IsPGroup p P) (hVP : ∀ y ∈ P, y ^ p = 1 → y ∈ V) {g : G}
    (hgP : g ∈ Subgroup.normalizer (P : Set G))
    (hg2 : g ^ 2 ∈ Subgroup.centralizer (P : Set G)) (hgV : ∀ v ∈ V, g * v * g⁻¹ = v) :
    g ∈ Subgroup.centralizer (P : Set G) := by
  classical
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  have hgy : g * y * g⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hgP y).mp hy
  set z := y⁻¹ * (g * y * g⁻¹) with hz
  have hzP : z ∈ P := P.mul_mem (P.inv_mem hy) hgy
  have hg2y : g * g * y = y * (g * g) := by
    have := Subgroup.mem_centralizer_iff.mp hg2 y hy
    rw [sq] at this
    exact this.symm
  have hzinv : ∀ n : ℕ, g * z ^ n * g⁻¹ = (z ^ n)⁻¹ := by
    have h1 : g * z * g⁻¹ = z⁻¹ := by
      rw [hz]
      calc g * (y⁻¹ * (g * y * g⁻¹)) * g⁻¹ = g * y⁻¹ * g⁻¹ * ((g * g * y) * g⁻¹ * g⁻¹) := by
            group
        _ = (y⁻¹ * (g * y * g⁻¹))⁻¹ := by rw [hg2y]; group
    intro n
    rw [← conj_pow, h1, inv_pow]
  by_contra hne
  have hz1 : z ≠ 1 := fun h => hne (by
    rw [hz] at h
    have : g * y * g⁻¹ = y := by
      calc g * y * g⁻¹ = y * (y⁻¹ * (g * y * g⁻¹)) := by group
        _ = y := by rw [h, mul_one]
    calc y * g = g * y * g⁻¹ * g := by rw [this]
      _ = g * y := by group)
  obtain ⟨n, hn⟩ := hPp ⟨z, hzP⟩
  have hn' : z ^ (p ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have hex : ∃ k, z ^ (p ^ k) = 1 := ⟨n, hn'⟩
  set k := Nat.find hex with hkdef
  have hk : z ^ (p ^ k) = 1 := Nat.find_spec hex
  have hk0 : k ≠ 0 := fun h => hz1 (by simpa [h] using hk)
  set j := k - 1 with hjdef
  have hkj : k = j + 1 := by omega
  have hw1 : z ^ (p ^ j) ≠ 1 := Nat.find_min hex (show j < k by omega)
  have hwp : (z ^ (p ^ j)) ^ p = 1 := by rw [← pow_mul, ← pow_succ, ← hkj]; exact hk
  have hwV : z ^ (p ^ j) ∈ V := hVP _ (P.pow_mem hzP _) hwp
  have h1 := hgV _ hwV
  rw [hzinv] at h1
  have hw2 : (z ^ (p ^ j)) ^ 2 = 1 := by
    rw [sq]
    calc z ^ (p ^ j) * z ^ (p ^ j) = (z ^ (p ^ j))⁻¹ * z ^ (p ^ j) := by rw [h1]
      _ = 1 := inv_mul_cancel _
  exact hw1 ((pow_eq_one_iff_of_coprime ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)).mp
    ⟨hwp, hw2⟩)

open scoped commutatorElement in
theorem key87 (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {a b : G} (hb : b ∈ A)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G} (hPp : IsPGroup p P)
    (hSP : (S : Subgroup G) ≤ Subgroup.normalizer (P : Set G))
    (hbP : ∀ x ∈ P, b⁻¹ * x * b = x⁻¹) (hrank : CFSG.Open.pRank p P = 2)
    (huniq : ∀ t ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (P : Set G), t ^ 2 = 1 →
      t = 1 ∨ t = a) (ha : a ∈ A) :
    (∀ u ∈ (S : Subgroup G), ∀ v ∈ (S : Subgroup G), u ^ 2 = 1 → v ^ 2 = 1 → u * v = v * u →
        u ∉ A → v ∉ A → u * v ∈ A) ∧
      (∀ u ∈ ⁅(S : Subgroup G), (S : Subgroup G)⁆, u ^ 2 = 1 → u ∈ A) ∧
      (∀ y ∈ ⁅(S : Subgroup G), (S : Subgroup G)⁆, y ^ 2 ∈ Subgroup.centralizer (P : Set G) →
        y ∈ Subgroup.centralizer (P : Set G) ∨ b * y ∈ Subgroup.centralizer (P : Set G)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy => comm_of_inv hbP hx hy
  obtain ⟨V, hVP, hVab, hVp, hVc, hVall⟩ := exists_omega1 hp hPab hrank
  have hSV : (S : Subgroup G) ≤ Subgroup.normalizer (V : Set G) := fun s hs =>
    mem_normalizer_of_conj_le fun v hv => by
      have h1 : s⁻¹ * v * s ∈ P := by
        simpa using (Subgroup.mem_normalizer_iff.mp (hSP (S.inv_mem hs)) v).mp (hVP hv)
      refine hVall _ h1 ?_
      have h2 := conj_pow (a := s⁻¹) (b := v) (i := p)
      rw [inv_inv, hVp v hv] at h2
      rw [h2]
      group
  obtain ⟨δ, hδ⟩ := exists_det hp2 hVab hVp hVc
  have hSA := le_centralizer hset h4
  have hbS : b ∈ (S : Subgroup G) := hset.le hb
  have hb2 : b * b = 1 := mul_self_eq_one hset.elem hb
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hbV : ∀ v ∈ V, b * v * b⁻¹ = v⁻¹ := fun v hv => by
    have h := hbP v (hVP hv)
    rw [hbi] at h ⊢
    exact h
  have hbu : ∀ u ∈ (S : Subgroup G), b * u = u * b := fun u hu =>
    Subgroup.mem_centralizer_iff.mp (hSA hu) b hb
  have hpm : ∀ y ∈ (S : Subgroup G), y ^ 2 ∈ Subgroup.centralizer (P : Set G) →
      ((∀ v ∈ V, y * v * y⁻¹ = v) ∨ (∀ v ∈ V, y * v * y⁻¹ = v⁻¹)) →
      y ∈ Subgroup.centralizer (P : Set G) ∨ b * y ∈ Subgroup.centralizer (P : Set G) := by
    intro y hy hy2 h
    rcases h with h | h
    · exact Or.inl (mem_centralizer_of_forall_eq hp hp2 hPp hVall (hSP hy) hy2 h)
    · refine Or.inr (mem_centralizer_of_forall_eq hp hp2 hPp hVall (hSP (S.mul_mem hbS hy)) ?_
        fun v hv => ?_)
      · have e : (b * y) ^ 2 = y ^ 2 := by
          rw [sq, sq]
          calc b * y * (b * y) = b * (y * b) * y := by group
            _ = b * (b * y) * y := by rw [hbu y hy]
            _ = (b * b) * (y * y) := by group
            _ = y * y := by rw [hb2, one_mul]
        rw [e]
        exact hy2
      · calc b * y * v * (b * y)⁻¹ = b * (y * v * y⁻¹) * b⁻¹ := by group
          _ = (b * v * b⁻¹)⁻¹ := by rw [h v hv]; group
          _ = v := by rw [hbV v hv, inv_inv]
  have hinvA : ∀ u ∈ (S : Subgroup G), u ^ 2 = 1 →
      ((∀ v ∈ V, u * v * u⁻¹ = v) ∨ (∀ v ∈ V, u * v * u⁻¹ = v⁻¹)) → u ∈ A := by
    intro u hu hu2 h
    rcases hpm u hu (by rw [hu2]; exact Subgroup.one_mem _) h with hC | hC
    · rcases huniq u ⟨hu, hC⟩ hu2 with h1 | h1
      · exact h1 ▸ A.one_mem
      · exact h1 ▸ ha
    · have hw2 : (b * u) ^ 2 = 1 := by
        rw [sq]
        calc b * u * (b * u) = b * (u * b) * u := by group
          _ = b * (b * u) * u := by rw [hbu u hu]
          _ = (b * b) * (u * u) := by group
          _ = 1 := by rw [hb2, ← sq, hu2, one_mul]
      rcases huniq (b * u) ⟨S.mul_mem hbS hu, hC⟩ hw2 with h1 | h1
      · have : u = b⁻¹ := eq_inv_of_mul_eq_one_right h1
        rw [this]
        exact A.inv_mem hb
      · have : u = b⁻¹ * a := by rw [← h1]; group
        rw [this]
        exact A.mul_mem (A.inv_mem hb) ha
  have hsq : ∀ y ∈ (S : Subgroup G), y ^ 2 ∈ Subgroup.centralizer (P : Set G) →
      ∀ v ∈ V, y * (y * v * y⁻¹) * y⁻¹ = v := fun y hy hy2 v hv => by
    have h := Subgroup.mem_centralizer_iff.mp hy2 v (hVP hv)
    calc y * (y * v * y⁻¹) * y⁻¹ = y ^ 2 * v * (y ^ 2)⁻¹ := by rw [sq]; group
      _ = v := by rw [← h]; group
  have hone : ∀ u (hu : u ∈ (S : Subgroup G)), u ^ 2 = 1 →
      δ ⟨u, hSV hu⟩ = 1 ∨ δ ⟨u, hSV hu⟩ = -1 := fun u hu hu2 => by
    refine mul_self_eq_one_iff.mp ?_
    rw [← map_mul]
    have : (⟨u, hSV hu⟩ * ⟨u, hSV hu⟩ : Subgroup.normalizer (V : Set G)) = 1 :=
      Subtype.ext (by rw [Subgroup.coe_mul, ← sq, hu2]; rfl)
    rw [this, map_one]
  have hneg : ∀ u (hu : u ∈ (S : Subgroup G)), u ^ 2 = 1 → u ∉ A → δ ⟨u, hSV hu⟩ = -1 := by
    intro u hu hu2 huA
    refine (hone u hu hu2).resolve_left fun h1 => huA (hinvA u hu hu2 ?_)
    exact hδ ⟨u, hSV hu⟩ (hsq u hu (by rw [hu2]; exact Subgroup.one_mem _)) h1
  refine ⟨fun u hu v hv hu2 hv2 huv huA hvA => ?_, fun u hu hu2 => ?_, fun y hy hy2 => ?_⟩
  · have huvS := S.mul_mem hu hv
    have huv2 : (u * v) ^ 2 = 1 := by
      rw [sq]
      calc u * v * (u * v) = u * (v * u) * v := by group
        _ = u * (u * v) * v := by rw [huv]
        _ = (u * u) * (v * v) := by group
        _ = 1 := by rw [← sq, ← sq, hu2, hv2, one_mul]
    refine hinvA _ huvS huv2 (hδ ⟨u * v, hSV huvS⟩
      (hsq _ huvS (by rw [huv2]; exact Subgroup.one_mem _)) ?_)
    have e : (⟨u * v, hSV huvS⟩ : Subgroup.normalizer (V : Set G)) =
        ⟨u, hSV hu⟩ * ⟨v, hSV hv⟩ := rfl
    rw [e, map_mul, hneg u hu hu2 huA, hneg v hv hv2 hvA]
    exact (neg_one_mul (-1 : ZMod p)).trans (neg_neg 1)
  · have huS : u ∈ (S : Subgroup G) := commutator_self_le _ hu
    exact hinvA u huS hu2 (hδ ⟨u, hSV huS⟩ (hsq u huS (by rw [hu2]; exact Subgroup.one_mem _))
      (det_eq_one_of_mem_commutator δ hSV hu _))
  · have hyS : y ∈ (S : Subgroup G) := commutator_self_le _ hy
    exact hpm y hyS hy2 (hδ ⟨y, hSV hyS⟩ (hsq y hyS hy2)
      (det_eq_one_of_mem_commutator δ hSV hy _))

end CFSG.Goldschmidt.Sec8
