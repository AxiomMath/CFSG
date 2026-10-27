module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.UGSChainNormalizerSylow
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GSThmB.CorC

open CFSG Subgroup
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem card_sup_mul_card_inf_of_commute {A B : Subgroup X}
    (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  let f : ↥A × ↥B →* X := A.subtype.noncommCoprod B.subtype fun m n => hAB m m.2 n n.2
  have hf : ∀ k : ↥A × ↥B, f k = (k.1 : X) * k.2 := fun k => rfl
  have hrange : f.range = A ⊔ B := by
    apply le_antisymm
    · rintro _ ⟨k, rfl⟩
      rw [hf]
      exact mul_mem (mem_sup_left k.1.2) (mem_sup_right k.2.2)
    · refine sup_le (fun x hx => ⟨(⟨x, hx⟩, 1), by rw [hf]; simp⟩) fun x hx =>
        ⟨(1, ⟨x, hx⟩), by rw [hf]; simp⟩
  have hmem : ∀ k : ↥A × ↥B, k ∈ f.ker ↔ (k.1 : X) * k.2 = 1 := fun k => by
    rw [MonoidHom.mem_ker, hf]
  have hker : Nat.card f.ker = Nat.card ↥(A ⊓ B) := by
    refine Nat.card_congr
      { toFun := fun k => ⟨(k.1.1 : X), mem_inf.mpr ⟨k.1.1.2, by
          rw [eq_inv_of_mul_eq_one_left ((hmem k.1).mp k.2)]
          exact inv_mem k.1.2.2⟩⟩
        invFun := fun c => ⟨(⟨c, (mem_inf.mp c.2).1⟩, ⟨(c : X)⁻¹, inv_mem (mem_inf.mp c.2).2⟩),
          (hmem _).mpr (mul_inv_cancel _)⟩
        left_inv := fun k => Subtype.ext (Prod.ext rfl (Subtype.ext
          (eq_inv_of_mul_eq_one_right ((hmem k.1).mp k.2)).symm))
        right_inv := fun c => rfl }
  have h := card_ker_mul_card_range f
  rw [hker, hrange, Nat.card_prod] at h
  rw [mul_comm]
  exact h

omit [Finite X] in
theorem commute_of_inf_eq_bot {H K : Subgroup X} (hHK : H ≤ normalizer (K : Set X))
    (hKH : K ≤ normalizer (H : Set X)) (hbot : H ⊓ K = ⊥) : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h := by
  intro h hh k hk
  have h1 : h * k * h⁻¹ * k⁻¹ ∈ K := mul_mem ((mem_normalizer_iff.mp (hHK hh) k).mp hk) (inv_mem hk)
  have h2 : h * k * h⁻¹ * k⁻¹ ∈ H := by
    have h3 : k * h⁻¹ * k⁻¹ ∈ H := (mem_normalizer_iff.mp (hKH hk) h⁻¹).mp (inv_mem hh)
    rw [show h * k * h⁻¹ * k⁻¹ = h * (k * h⁻¹ * k⁻¹) by group]
    exact mul_mem hh h3
  have h4 : h * k * h⁻¹ * k⁻¹ ∈ H ⊓ K := mem_inf.mpr ⟨h2, h1⟩
  rw [hbot, mem_bot] at h4
  calc h * k = h * k * h⁻¹ * k⁻¹ * (k * h) := by group
    _ = k * h := by rw [h4, one_mul]

omit [Finite X] in
theorem le_normalizer_of_commute {A B : Subgroup X} (h : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    A ≤ normalizer (B : Set X) := fun x hx => mem_normalizer_iff.mpr fun y => by
  constructor
  · intro hy
    rw [h x hx y hy, mul_inv_cancel_right]
    exact hy
  · intro hy
    have h1 := h x hx _ hy
    have h2 : y = x * y * x⁻¹ := by
      calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
        _ = x⁻¹ * (x * (x * y * x⁻¹)) * x⁻¹ * x := by rw [h1]; group
        _ = x * y * x⁻¹ := by group
    rw [h2]
    exact hy

theorem exists_involution_center_of_normal {S N : Subgroup X} (hS2 : IsPGroup 2 S)
    (hNS : N ≤ S) (hSN : S ≤ normalizer (N : Set X)) (hN : N ≠ ⊥) :
    ∃ q ∈ N, orderOf q = 2 ∧ ∀ s ∈ S, s * q = q * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥S := hS2.isNilpotent
  have hN'n : (N.subgroupOf S).Normal := (normal_subgroupOf_iff_le_normalizer hNS).mpr hSN
  have hN'ne : N.subgroupOf S ≠ ⊥ := by
    intro hbot
    apply hN
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hNS hx⟩ : S) ∈ N.subgroupOf S := hx
    rw [hbot, mem_bot] at h1
    exact mem_bot.mpr (congrArg Subtype.val h1)
  have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hN'ne
  have hZ2 : IsPGroup 2 ↥(N.subgroupOf S ⊓ center ↥S) := hS2.to_subgroup _
  have : Nontrivial ↥(N.subgroupOf S ⊓ center ↥S) := (nontrivial_iff_ne_bot _).mpr hZ
  obtain ⟨k, hk0, hk⟩ := hZ2.nontrivial_iff_card.mp this
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [hk]; exact dvd_pow_self 2 hk0.ne')
  refine ⟨((x : S) : X), (mem_inf.mp x.2).1, ?_, fun s hs => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  · exact congrArg Subtype.val (mem_center_iff.mp (mem_inf.mp x.2).2 ⟨s, hs⟩)

theorem exists_mem_normalizer_conj {a z g : X} {S : Subgroup X}
    (hSa : S ≤ centralizer ({a} : Set X))
    (hSsyl : ∃ T : Sylow 2 ↥(centralizer ({a} : Set X)),
      (T : Subgroup _) = S.subgroupOf (centralizer ({a} : Set X)))
    (hzS : ∀ s ∈ S, s * z = z * s) (hg : g * a * g⁻¹ = a * z) :
    ∃ n : X, n ∈ normalizer (S : Set X) ∧ n * a * n⁻¹ = a * z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := hSsyl
  have hφa : (MulAut.conj g) a = a * z := by rw [MulAut.conj_apply, hg]
  have hC₂eq : (centralizer ({a} : Set X)).map (MulAut.conj g).toMonoidHom =
      centralizer ({a * z} : Set X) := by
    rw [UGSChain.map_centralizer_singleton, hφa]
  have hcardC : Nat.card ↥(centralizer ({a * z} : Set X)) =
      Nat.card ↥(centralizer ({a} : Set X)) := by
    rw [← hC₂eq, card_map_of_injective (MulAut.conj g).injective]
  have hSC₂ : S ≤ centralizer ({a * z} : Set X) := by
    intro s hs
    rw [mem_centralizer_singleton_iff]
    have h1 := mem_centralizer_singleton_iff.mp (hSa hs)
    calc s * (a * z) = (s * a) * z := by group
      _ = a * (s * z) := by rw [h1]; group
      _ = a * (z * s) := by rw [hzS s hs]
      _ = a * z * s := by group
  have hcardS : Nat.card S = 2 ^ (Nat.card ↥(centralizer ({a * z} : Set X))).factorization 2 := by
    rw [hcardC, ← Sylow.card_eq_multiplicity T, hT,
      Nat.card_congr (subgroupOfEquivOfLe hSa).toEquiv]
  have hgSC₂ : S.map (MulAut.conj g).toMonoidHom ≤ centralizer ({a * z} : Set X) := by
    rw [← hC₂eq]
    exact map_mono hSa
  have hcardgS : Nat.card ↥(S.map (MulAut.conj g).toMonoidHom) = Nat.card S :=
    card_map_of_injective (MulAut.conj g).injective
  let S₂ : Sylow 2 ↥(centralizer ({a * z} : Set X)) := Sylow.ofCard (S.subgroupOf _)
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hSC₂).toEquiv, hcardS])
  let S₃ : Sylow 2 ↥(centralizer ({a * z} : Set X)) :=
    Sylow.ofCard ((S.map (MulAut.conj g).toMonoidHom).subgroupOf _)
      (by rw [Nat.card_congr (subgroupOfEquivOfLe hgSC₂).toEquiv, hcardgS, hcardS])
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥(centralizer ({a * z} : Set X))) S₃ S₂
  refine ⟨(c : X) * g, ?_, ?_⟩
  · rw [mem_normalizer_iff_map_conj_eq]
    refine eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (MulAut.conj _).injective])
    rintro _ ⟨s, hs, rfl⟩
    have h1 : (⟨g * s * g⁻¹, hgSC₂ ⟨s, hs, rfl⟩⟩ : ↥(centralizer ({a * z} : Set X))) ∈
        (S₃ : Subgroup ↥(centralizer ({a * z} : Set X))) := ⟨s, hs, rfl⟩
    have h2 := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj c) _ h1
    rw [← Sylow.coe_subgroup_smul, hc] at h2
    have h3 : ((MulAut.conj c • (⟨g * s * g⁻¹, hgSC₂ ⟨s, hs, rfl⟩⟩ :
        ↥(centralizer ({a * z} : Set X))) : ↥(centralizer ({a * z} : Set X))) : X) ∈ S := h2
    rw [MulAut.smul_def, MulAut.conj_apply] at h3
    simp only [coe_mul, coe_inv] at h3
    show (c : X) * g * s * ((c : X) * g)⁻¹ ∈ S
    rwa [show (c : X) * g * s * ((c : X) * g)⁻¹ = c * (g * s * g⁻¹) * (c : X)⁻¹ by group]
  · have hc' : (c : X) * (a * z) = a * z * c := mem_centralizer_singleton_iff.mp c.2
    calc (c : X) * g * a * ((c : X) * g)⁻¹ = c * (g * a * g⁻¹) * (c : X)⁻¹ := by group
      _ = a * z := by rw [hg, hc']; group

theorem centralizes_of_count {S P D Q : Subgroup X} (hDS : D ≤ S) (hPS : P ≤ S) (hQS : Q ≤ S)
    (hDP : ∀ d ∈ D, ∀ p ∈ P, d * p = p * d) (hDQ : ∀ d ∈ D, ∀ q ∈ Q, d * q = q * d)
    (hPQ : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) (hDPb : D ⊓ P = ⊥) (hPQb : P ⊓ Q = ⊥)
    (hQP : Nat.card Q = Nat.card P) (hS : Nat.card S ≤ 16 * Nat.card P) (hD : 8 ≤ Nat.card D)
    (hZD : Nat.card ↥(D ⊓ centralizer (D : Set X)) ≤ 2) (hP4 : 4 ≤ Nat.card P) :
    ∀ s ∈ S, ∀ p ∈ P, s * p = p * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPpos : 0 < Nat.card P := Nat.card_pos
  have h1 := card_sup_mul_card_inf_of_commute hDP
  rw [hDPb, card_bot, mul_one] at h1
  have hWZ : (D ⊔ P) ⊓ Q ⊔ P ≤ D ⊓ centralizer (D : Set X) ⊔ P := by
    refine sup_le (fun w hw => ?_) le_sup_right
    obtain ⟨hwDP, hwQ⟩ := mem_inf.mp hw
    have hw' : w ∈ ((D ⊔ P : Subgroup X) : Set X) := hwDP
    rw [coe_mul_of_left_le_normalizer_right D P (le_normalizer_of_commute hDP)] at hw'
    obtain ⟨d, hd, p, hp, rfl⟩ := hw'
    have hdC : d ∈ centralizer (D : Set X) := by
      rw [mem_centralizer_iff]
      intro x hx
      have h2 := hDQ x hx _ hwQ
      have h3 := hDP x hx p hp
      have h4 : x * d * p = d * x * p := by
        calc x * d * p = x * (d * p) := by group
          _ = d * p * x := h2
          _ = d * (x * p) := by rw [mul_assoc, h3]
          _ = d * x * p := by group
      exact mul_right_cancel h4
    exact mul_mem (mem_sup_left (mem_inf.mpr ⟨hd, hdC⟩)) (mem_sup_right hp)
  have h2 := card_sup_mul_card_inf_of_commute (A := (D ⊔ P) ⊓ Q) (B := P)
    fun w hw p hp => (hPQ p hp w (mem_inf.mp hw).2).symm
  have hWP : (D ⊔ P) ⊓ Q ⊓ P = ⊥ := by
    rw [eq_bot_iff, ← hPQb]
    intro x hx
    exact mem_inf.mpr ⟨(mem_inf.mp hx).2, (mem_inf.mp (mem_inf.mp hx).1).2⟩
  rw [hWP, card_bot, mul_one] at h2
  have h3 := card_sup_mul_card_inf_of_commute (A := D ⊓ centralizer (D : Set X)) (B := P)
    fun x hx p hp => hDP x (mem_inf.mp hx).1 p hp
  have hZP : D ⊓ centralizer (D : Set X) ⊓ P = ⊥ := by
    rw [eq_bot_iff, ← hDPb]
    exact inf_le_inf_right P inf_le_left
  rw [hZP, card_bot, mul_one] at h3
  have h4 := card_le_of_le hWZ
  rw [h2, h3] at h4
  have hW2 : Nat.card ↥((D ⊔ P) ⊓ Q) ≤ 2 :=
    le_trans (Nat.le_of_mul_le_mul_right h4 hPpos) hZD
  have hDPQ : ∀ x ∈ D ⊔ P, ∀ q ∈ Q, x * q = q * x := by
    have hle : D ⊔ P ≤ centralizer (Q : Set X) := sup_le
      (fun d hd => mem_centralizer_iff.mpr fun q hq => (hDQ d hd q hq).symm)
      (fun p hp => mem_centralizer_iff.mpr fun q hq => (hPQ p hp q hq).symm)
    intro x hx q hq
    exact (mem_centralizer_iff.mp (hle hx) q hq).symm
  have h5 := card_sup_mul_card_inf_of_commute hDPQ
  rw [h1, hQP] at h5
  have hTS : D ⊔ P ⊔ Q ≤ S := sup_le (sup_le hDS hPS) hQS
  have h6 := card_le_of_le hTS
  have h7 : Nat.card D * Nat.card P * Nat.card P ≤ 32 * Nat.card P := by
    rw [← h5]
    calc Nat.card ↥(D ⊔ P ⊔ Q) * Nat.card ↥((D ⊔ P) ⊓ Q) ≤ Nat.card ↥(D ⊔ P ⊔ Q) * 2 :=
          Nat.mul_le_mul_left _ hW2
      _ ≤ Nat.card S * 2 := Nat.mul_le_mul_right _ h6
      _ ≤ 16 * Nat.card P * 2 := Nat.mul_le_mul_right _ hS
      _ = 32 * Nat.card P := by ring
  have h8 : Nat.card D * Nat.card P ≤ 32 := Nat.le_of_mul_le_mul_right h7 hPpos
  have hP : Nat.card P = 4 := by nlinarith
  have hTeq : D ⊔ P ⊔ Q = S := by
    refine eq_of_le_of_card_ge hTS ?_
    rw [hP] at h5 hS
    nlinarith
  have hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    have hcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (G := ↥P)
      (by rw [hP]; norm_num)
    intro x hx y hy
    exact congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hSC : S ≤ centralizer (P : Set X) := by
    rw [← hTeq]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact fun d hd => mem_centralizer_iff.mpr fun p hp => (hDP d hd p hp).symm
    · exact fun x hx => mem_centralizer_iff.mpr fun p hp => hPc p hp x hx
    · exact fun q hq => mem_centralizer_iff.mpr fun p hp => hPQ p hp q hq
  intro s hs p hp
  exact (mem_centralizer_iff.mp (hSC hs) p hp).symm

end CFSG.ComponentClassification.GSThmB.CorC
