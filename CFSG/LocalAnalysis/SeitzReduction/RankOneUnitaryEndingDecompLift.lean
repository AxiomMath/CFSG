module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingProduct
public import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem exists_eq_mul_of_fpf [Finite G] {H R : Subgroup G} {g : G} (hRH : R ≤ H)
    (hRn : ∀ r ∈ R, ∀ x ∈ H, x * r * x⁻¹ ∈ R) (hgH : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (hgR : ∀ r ∈ R, g * r * g⁻¹ ∈ R)
    (hfpf : ∀ x ∈ H, g * x * g⁻¹ * x⁻¹ ∈ R → x ∈ R) :
    ∀ y ∈ H, ∃ x ∈ H, ∃ r ∈ R, y = x⁻¹ * (g * x * g⁻¹) * r := by
  set N : Subgroup H := R.subgroupOf H with hN
  have hNn : N.Normal :=
    (normal_subgroupOf_iff hRH).mpr fun r x hr hx => hRn r hr x hx
  let φ : H →* H := MonoidHom.mk' (fun x => ⟨g * x * g⁻¹, hgH x x.2⟩) (fun a b => by
    ext
    simp only [Subgroup.coe_mul]
    group)
  have hφN : N ≤ N.comap φ := by
    intro x hx
    simp only [mem_comap, hN, mem_subgroupOf] at hx ⊢
    exact hgR _ hx
  let α : H ⧸ N →* H ⧸ N := QuotientGroup.map N N φ hφN
  have hfix : ∀ c : H ⧸ N, α c = c → c = 1 := by
    intro c
    induction c using QuotientGroup.induction_on with
    | H x =>
      intro hc
      rw [QuotientGroup.map_mk] at hc
      have h1 : (x : H)⁻¹ * φ x ∈ N := QuotientGroup.eq.mp hc.symm
      rw [hN, mem_subgroupOf] at h1
      have h2 : g * (x : G) * g⁻¹ * (x : G)⁻¹ ∈ R := by
        have h3 := hRn _ h1 (x : G) x.2
        have e : (x : G) * ((x : H)⁻¹ * φ x : H) * (x : G)⁻¹ =
            g * (x : G) * g⁻¹ * (x : G)⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.mk'_apply, φ]
          group
        rw [e] at h3
        exact h3
      have hx : (x : G) ∈ R := hfpf _ x.2 h2
      exact (QuotientGroup.eq_one_iff (x : H)).mpr (by rw [hN, mem_subgroupOf]; exact hx)
  let β : H ⧸ N → H ⧸ N := fun c => c⁻¹ * α c
  have hβ : Function.Injective β := by
    intro c c' h
    have e1 : c' * c⁻¹ = α (c' * c⁻¹) := by
      have : c' * (c⁻¹ * α c) * (α c)⁻¹ = c' * (c'⁻¹ * α c') * (α c)⁻¹ := by
        simp only [β] at h
        rw [h]
      rw [map_mul, map_inv]
      calc c' * c⁻¹ = c' * (c⁻¹ * α c) * (α c)⁻¹ := by group
        _ = c' * (c'⁻¹ * α c') * (α c)⁻¹ := this
        _ = α c' * (α c)⁻¹ := by group
    have e2 := hfix _ e1.symm
    calc c = c' * c⁻¹ * c := by rw [e2, one_mul]
      _ = c' := by group
  have hβs : Function.Surjective β := Finite.injective_iff_surjective.mp hβ
  intro y hy
  obtain ⟨c, hc⟩ := hβs ((⟨y, hy⟩ : H) : H ⧸ N)
  induction c using QuotientGroup.induction_on with
  | H x =>
    refine ⟨x, x.2, (g * (x : G) * g⁻¹)⁻¹ * x * y, ?_, by group⟩
    have hc' : ((x⁻¹ * φ x : H) : H ⧸ N) = ((⟨y, hy⟩ : H) : H ⧸ N) := by
      simp only [β, QuotientGroup.map_mk, α] at hc
      rw [← hc]
      rfl
    have h1 := QuotientGroup.eq.mp hc'
    rw [hN, mem_subgroupOf] at h1
    simpa [φ, mul_assoc] using h1

theorem exists_complement_of_fpf [Finite G] {J R Z : Subgroup G} {g : G} {o : ℕ} (hZR : Z ≤ R)
    (hRJ : R ≤ J) (hJR : ∀ x ∈ J, ∀ r ∈ R, x * r = r * x)
    (hJZ : ∀ x ∈ J, ∀ y ∈ J, x * y * x⁻¹ * y⁻¹ ∈ Z) (hsq : ∀ r ∈ R, r ^ 2 = 1)
    (hgJ : ∀ x ∈ J, g * x * g⁻¹ ∈ J) (hgR : ∀ r ∈ R, g * r * g⁻¹ = r) (ho : Odd o)
    (hgo : g ^ o = 1) (hfpf : ∀ x ∈ J, g * x * g⁻¹ * x⁻¹ ∈ R → x ∈ R) :
    ∃ Y : Subgroup G, Y ≤ J ∧ Z ≤ Y ∧ Y ⊓ R ≤ Z ∧ ∀ x ∈ J, ∃ y ∈ Y, ∃ r ∈ R, x = y * r := by
  have hcz : ∀ z ∈ R, ∀ x ∈ J, z * x = x * z := fun z hz x hx => (hJR x hx z hz).symm
  let Y : Subgroup G :=
    { carrier := {x | x ∈ J ∧ ∃ y ∈ J, ∃ z ∈ Z, x = y⁻¹ * (g * y * g⁻¹) * z}
      one_mem' := ⟨one_mem _, 1, one_mem _, 1, one_mem _, by group⟩
      mul_mem' := by
        rintro _ _ ⟨hx, y, hy, z, hz, rfl⟩ ⟨hx', y', hy', z', hz', rfl⟩
        refine ⟨mul_mem hx hx', y * y', mul_mem hy hy',
          ((g * y * g⁻¹)⁻¹ * y) * y' * ((g * y * g⁻¹)⁻¹ * y)⁻¹ * y'⁻¹ * z * z', ?_, ?_⟩
        · have hw : (g * y * g⁻¹)⁻¹ * y ∈ J := mul_mem (inv_mem (hgJ y hy)) hy
          exact mul_mem (mul_mem (hJZ _ hw _ hy') hz) hz'
        · have hgy' : y'⁻¹ * (g * y' * g⁻¹) ∈ J := mul_mem (inv_mem hy') (hgJ y' hy')
          have hw : (g * y * g⁻¹)⁻¹ * y ∈ J := mul_mem (inv_mem (hgJ y hy)) hy
          have hc := hJZ _ hw _ hy'
          calc y⁻¹ * (g * y * g⁻¹) * z * (y'⁻¹ * (g * y' * g⁻¹) * z') =
              y⁻¹ * (g * y * g⁻¹) * (z * (y'⁻¹ * (g * y' * g⁻¹))) * z' := by group
            _ = y⁻¹ * (g * y * g⁻¹) * ((y'⁻¹ * (g * y' * g⁻¹)) * z) * z' := by
                rw [hcz z (hZR hz) _ hgy']
            _ = y'⁻¹ * y⁻¹ * (g * y * g⁻¹) *
                (((g * y * g⁻¹)⁻¹ * y) * y' * ((g * y * g⁻¹)⁻¹ * y)⁻¹ * y'⁻¹ *
                  (g * y' * g⁻¹)) * z * z' := by group
            _ = y'⁻¹ * y⁻¹ * (g * y * g⁻¹) * ((g * y' * g⁻¹) *
                (((g * y * g⁻¹)⁻¹ * y) * y' * ((g * y * g⁻¹)⁻¹ * y)⁻¹ * y'⁻¹)) * z * z' := by
                rw [hcz _ (hZR hc) _ (hgJ y' hy')]
            _ = (y * y')⁻¹ * (g * (y * y') * g⁻¹) *
                (((g * y * g⁻¹)⁻¹ * y) * y' * ((g * y * g⁻¹)⁻¹ * y)⁻¹ * y'⁻¹ * z * z') := by
                group
      inv_mem' := by
        rintro _ ⟨hx, y, hy, z, hz, rfl⟩
        refine ⟨inv_mem hx, y⁻¹, inv_mem hy,
          (g * y * g⁻¹) * y⁻¹ * (g * y * g⁻¹)⁻¹ * y * z⁻¹, ?_, ?_⟩
        · have h1 := hJZ _ (hgJ y hy) _ (inv_mem hy)
          rw [inv_inv] at h1
          exact mul_mem h1 (inv_mem hz)
        · have hgy : (g * y * g⁻¹)⁻¹ * y ∈ J := mul_mem (inv_mem (hgJ y hy)) hy
          calc (y⁻¹ * (g * y * g⁻¹) * z)⁻¹ = z⁻¹ * ((g * y * g⁻¹)⁻¹ * y) := by group
            _ = ((g * y * g⁻¹)⁻¹ * y) * z⁻¹ := by
                rw [hcz _ (hZR (inv_mem hz)) _ hgy]
            _ = y⁻¹⁻¹ * (g * y⁻¹ * g⁻¹) *
                ((g * y * g⁻¹) * y⁻¹ * (g * y * g⁻¹)⁻¹ * y * z⁻¹) := by group }
  have hmemY : ∀ x : G, x ∈ Y ↔ x ∈ J ∧ ∃ y ∈ J, ∃ z ∈ Z, x = y⁻¹ * (g * y * g⁻¹) * z :=
    fun x => Iff.rfl
  refine ⟨Y, fun x hx => ((hmemY x).mp hx).1, fun z hz => (hmemY z).mpr
    ⟨hRJ (hZR hz), 1, one_mem _, z, hz, by group⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxY, hxR⟩ := mem_inf.mp hx
    obtain ⟨-, y, hy, z, hz, rfl⟩ := (hmemY _).mp hxY
    set p := y⁻¹ * (g * y * g⁻¹) with hp
    have hpR : p ∈ R := by
      have := mul_mem hxR (inv_mem (hZR hz))
      rwa [mul_inv_cancel_right] at this
    have hpow : ∀ i : ℕ, g ^ i * y * (g ^ i)⁻¹ = y * p ^ i := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        have hgp : g * p ^ i * g⁻¹ = p ^ i := by
          rw [← conj_pow, hgR p hpR]
        calc g ^ (i + 1) * y * (g ^ (i + 1))⁻¹ = g * (g ^ i * y * (g ^ i)⁻¹) * g⁻¹ := by
              rw [pow_succ']; group
          _ = (g * y * g⁻¹) * (g * p ^ i * g⁻¹) := by rw [ih]; group
          _ = y * p ^ (i + 1) := by
              have hyp : g * y * g⁻¹ = y * p := by rw [hp]; group
              rw [hgp, hyp, pow_succ', mul_assoc]
    have h1 := hpow o
    rw [hgo, one_mul, inv_one, mul_one] at h1
    have hpo : p ^ o = 1 := by
      have := congrArg (fun w => y⁻¹ * w) h1
      simpa using this.symm
    obtain ⟨k, rfl⟩ := ho
    have hp1 : p = 1 := by
      rw [pow_succ, pow_mul, hsq p hpR, one_pow, one_mul] at hpo
      exact hpo
    rw [hp1, one_mul]
    exact hz
  · intro x hx
    have hRn : ∀ r ∈ R, ∀ x ∈ J, x * r * x⁻¹ ∈ R := fun r hr x hx => by
      rw [hJR x hx r hr, mul_inv_cancel_right]
      exact hr
    have hgR' : ∀ r ∈ R, g * r * g⁻¹ ∈ R := fun r hr => by rw [hgR r hr]; exact hr
    obtain ⟨y, hy, r, hr, rfl⟩ := exists_eq_mul_of_fpf hRJ hRn hgJ hgR' hfpf x hx
    exact ⟨y⁻¹ * (g * y * g⁻¹), (hmemY _).mpr ⟨mul_mem (inv_mem hy) (hgJ y hy), y, hy, 1,
      one_mem _, by group⟩, r, hr, rfl⟩

theorem conj_mem_commutator_of_conj {J J' : Subgroup G} {c : G}
    (h : ∀ x ∈ J, c * x * c⁻¹ ∈ J') : ∀ z ∈ ⁅J, J⁆, c * z * c⁻¹ ∈ ⁅J', J'⁆ := by
  have hle : ⁅J, J⁆ ≤ ⁅J', J'⁆.comap (MulAut.conj c).toMonoidHom := by
    rw [commutator_le]
    intro a ha b hb
    simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have e : c * ⁅a, b⁆ * c⁻¹ = ⁅c * a * c⁻¹, c * b * c⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact commutator_mem_commutator (h a ha) (h b hb)
  intro z hz
  simpa [MulAut.conj_apply] using hle hz

theorem mem_normalizer_commutator {J : Subgroup G} {d : G} (hd : d ∈ normalizer (J : Set G)) :
    d ∈ normalizer ((⁅J, J⁆ : Subgroup G) : Set G) := by
  have h1 : ∀ x ∈ J, d * x * d⁻¹ ∈ J := fun x hx => (mem_normalizer_iff.mp hd x).mp hx
  have h2 : ∀ x ∈ J, d⁻¹ * x * d⁻¹⁻¹ ∈ J := fun x hx =>
    (mem_normalizer_iff.mp (inv_mem hd) x).mp hx
  refine mem_normalizer_iff.mpr fun z => ⟨fun hz => conj_mem_commutator_of_conj h1 z hz,
    fun hz => ?_⟩
  have := conj_mem_commutator_of_conj h2 _ hz
  rwa [show d⁻¹ * (d * z * d⁻¹) * d⁻¹⁻¹ = z by group] at this

end CFSG.SeitzReduction.RankOne
