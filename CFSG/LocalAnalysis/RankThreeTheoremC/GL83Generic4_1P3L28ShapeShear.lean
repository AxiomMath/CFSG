module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Shape

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem l28z_comm {P : Subgroup G} {z : G} (hz : z ∈ L28Z P) {g : G} (hg : g ∈ P) :
    g * z = z * g := by
  obtain ⟨z', hz', rfl⟩ := hz
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz' ⟨g, hg⟩)

omit [Finite G] in
theorem mem_l28Z_of_comm {P : Subgroup G} {z : G} (hzP : z ∈ P) (h : ∀ g ∈ P, g * z = z * g) :
    z ∈ L28Z P :=
  ⟨⟨z, hzP⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext (h g g.2), rfl⟩

omit [Finite G] in
theorem l28Z_le (P : Subgroup G) : L28Z P ≤ P := by
  rintro _ ⟨z, -, rfl⟩
  exact z.2

theorem L28Shape.toShear {p : ℕ} {P : Subgroup G} (hZc : Nat.card (L28Z P) = p ^ 2)
    (h : L28Shape p P) : L28Shear p P := by
  obtain ⟨-, K, hKP, hKmax, ⟨e⟩, -, ⟨A, B, -, -, -, hABK, hAn, hBn⟩, hZ⟩ := h
  have hKP' : K ≤ P := hKP.le
  have hZK : L28Z P ≤ K := fun z hz => ((hZ z).mp hz).1
  have hKab : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
    intro a ha b hb
    have h1 := e.injective (show e (⟨a, ha⟩ * ⟨b, hb⟩) = e (⟨b, hb⟩ * ⟨a, ha⟩) by
      rw [map_mul, map_mul, mul_comm])
    exact congrArg Subtype.val h1
  have hm : ∀ m : Multiplicative (ZMod (p ^ 2)), m ^ (p ^ 2) = 1 := fun m => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hKexp : ∀ a ∈ K, a ^ (p ^ 2) = 1 := by
    intro a ha
    have h1 : e ((⟨a, ha⟩ : ↥K) ^ (p ^ 2)) = 1 := by
      rw [map_pow]
      exact Prod.ext (hm _) (hm _)
    have h2 := e.injective (h1.trans (map_one e).symm)
    simpa using congrArg Subtype.val h2
  have hKc : Nat.card K = p ^ 4 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod]
    ring
  have hKn : ∀ g ∈ P, ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    intro g hg k hk
    have hA := mem_normalizer_iff_map_conj_eq.mp (hAn hg)
    have hB := mem_normalizer_iff_map_conj_eq.mp (hBn hg)
    have hKg : K.map (MulAut.conj g).toMonoidHom = K := by
      rw [← hABK, Subgroup.map_sup]
      exact congrArg₂ (· ⊔ ·) hA hB
    have hk' : (MulAut.conj g).toMonoidHom k ∈ K.map (MulAut.conj g).toMonoidHom :=
      mem_map_of_mem _ hk
    rw [hKg] at hk'
    simpa [MulAut.conj_apply] using hk'
  have hp0 : 0 < p := by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp at hZc
      exact absurd hZc (Nat.card_pos (α := L28Z P)).ne'
    · exact hp
  refine ⟨⟨⟨⟨fun a b => Subtype.ext (l28z_comm b.2 (l28Z_le P a.2))⟩⟩,
    fun z hz => ((hZ z).mp hz).2⟩, ?_⟩
  intro u huP hup huZ z hzZ
  have huK : u ∉ K := fun hK => huZ ((hZ u).mpr ⟨hK, hup⟩)
  have hPK : K ⊔ zpowers u = P := by
    refine hKmax _ (lt_of_le_of_ne le_sup_left fun h' => huK ?_) (sup_le hKP' (zpowers_le.mpr huP))
    have hu : u ∈ K ⊔ zpowers u := Subgroup.mem_sup_right (mem_zpowers u)
    rwa [← h'] at hu
  have hKu : ∀ k ∈ K, u * k * u⁻¹ ∈ K := hKn u huP
  let θ : ↥K →* ↥K := MonoidHom.mk' (fun q => ⟨q.1 * (u * q.1⁻¹ * u⁻¹),
      K.mul_mem q.2 (hKu _ (K.inv_mem q.2))⟩) (by
    intro q q'
    apply Subtype.ext
    show q.1 * q'.1 * (u * (q.1 * q'.1)⁻¹ * u⁻¹) =
      q.1 * (u * q.1⁻¹ * u⁻¹) * (q'.1 * (u * q'.1⁻¹ * u⁻¹))
    have hc : u * (q.1 * q'.1)⁻¹ * u⁻¹ = (u * q'.1⁻¹ * u⁻¹) * (u * q.1⁻¹ * u⁻¹) := by group
    have h1 := hKab q'.1 q'.2 (u * q.1⁻¹ * u⁻¹) (hKu _ (K.inv_mem q.2))
    have h2 := hKab (u * q.1⁻¹ * u⁻¹) (hKu _ (K.inv_mem q.2)) (u * q'.1⁻¹ * u⁻¹)
      (hKu _ (K.inv_mem q'.2))
    rw [hc]
    calc q.1 * q'.1 * (u * q'.1⁻¹ * u⁻¹ * (u * q.1⁻¹ * u⁻¹))
        = q.1 * q'.1 * (u * q.1⁻¹ * u⁻¹ * (u * q'.1⁻¹ * u⁻¹)) := by rw [h2]
      _ = q.1 * (q'.1 * (u * q.1⁻¹ * u⁻¹)) * (u * q'.1⁻¹ * u⁻¹) := by simp only [mul_assoc]
      _ = q.1 * ((u * q.1⁻¹ * u⁻¹) * q'.1) * (u * q'.1⁻¹ * u⁻¹) := by rw [h1]
      _ = q.1 * (u * q.1⁻¹ * u⁻¹) * (q'.1 * (u * q'.1⁻¹ * u⁻¹)) := by simp only [mul_assoc])
  have hθ : ∀ q : ↥K, (θ q).1 = q.1 * (u * q.1⁻¹ * u⁻¹) := fun q => rfl
  have hker : θ.ker = (L28Z P).subgroupOf K := by
    ext ⟨q, hqK⟩
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have h1' : q * (u * q⁻¹ * u⁻¹) = 1 := congrArg Subtype.val h1
      have hqu : q * u = u * q := by
        calc q * u = (q * (u * q⁻¹ * u⁻¹)) * u * q := by group
          _ = u * q := by rw [h1']; group
      have hPq : P ≤ centralizer ({q} : Set G) := by
        rw [← hPK]
        exact sup_le (fun k hk => mem_centralizer_singleton_iff.mpr (hKab k hk q hqK))
          (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hqu.symm))
      exact mem_l28Z_of_comm (hKP' hqK) fun g hg => mem_centralizer_singleton_iff.mp (hPq hg)
    · intro hqZ
      apply Subtype.ext
      show q * (u * q⁻¹ * u⁻¹) = 1
      have hcomm := l28z_comm hqZ huP
      calc q * (u * q⁻¹ * u⁻¹) = (q * u * q⁻¹) * u⁻¹ := by group
        _ = 1 := by rw [← hcomm]; group
  have hkercard : Nat.card θ.ker = p ^ 2 := by
    rw [hker, ← hZc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv
  have hrange : θ.range ≤ (L28Z P).subgroupOf K := by
    rintro _ ⟨q, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    refine (hZ _).mpr ⟨(θ q).2, ?_⟩
    have h2 : q ^ p ∈ θ.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      refine (hZ _).mpr ⟨(q ^ p).2, ?_⟩
      rw [Subgroup.coe_pow, ← pow_mul, ← sq]
      exact hKexp q.1 q.2
    have h3 : (θ q) ^ p = 1 := by rw [← map_pow]; exact h2
    simpa using congrArg Subtype.val h3
  have hrc : Nat.card θ.range = p ^ 2 := by
    have h1 := Subgroup.card_ker_mul_card_range θ
    rw [hkercard, hKc] at h1
    have h2 : p ^ 2 * Nat.card θ.range = p ^ 2 * p ^ 2 := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp0 2) h2
  have hrange_eq : θ.range = (L28Z P).subgroupOf K := by
    refine Subgroup.eq_of_le_of_card_ge hrange ?_
    rw [hrc, ← hZc]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv).le
  have hzK : z ∈ K := hZK hzZ
  have hzr : (⟨z, hzK⟩ : ↥K) ∈ θ.range := by
    rw [hrange_eq, Subgroup.mem_subgroupOf]
    exact hzZ
  obtain ⟨q, hq⟩ := hzr
  have hq' : q.1 * (u * q.1⁻¹ * u⁻¹) = z := congrArg Subtype.val hq
  refine ⟨q.1, hKP' q.2, ?_⟩
  calc q.1 * u * q.1⁻¹ = (q.1 * (u * q.1⁻¹ * u⁻¹)) * u := by group
    _ = z * u := by rw [hq']
    _ = u * z := (l28z_comm hzZ huP).symm

end CFSG.LocalAnalysis.RankThreeTheoremC
