module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGen
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem elemAbelian_comm {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := by
  haveI : IsMulCommutative E := hE.1
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : E) (⟨b, hb⟩ : E))

private theorem elemAbelian_inv {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E) {a : G}
    (ha : a ∈ E) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hE.2 a ha)

private theorem four_le_card_inf_centralizer_of_card_eight {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 2 E) (hcard : Nat.card E = 8) {v : G}
    (hnorm : ∀ e ∈ E, v * e * v⁻¹ ∈ E) (hv2 : v * v = 1) :
    4 ≤ Nat.card ↥(E ⊓ centralizer ({v} : Set G)) := by
  have hvv : v * v = 1 := hv2
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_left hv2
  have hvE : ∀ e ∈ E, v * e * v ∈ E := fun e he => by
    simpa [hvinv] using hnorm e he
  let φ : E →* E :=
    { toFun := fun e => ⟨(e : G) * (v * (e : G) * v), E.mul_mem e.2 (hvE (e : G) e.2)⟩
      map_one' := Subtype.ext (by
        change (1 : G) * (v * 1 * v) = 1
        rw [one_mul, mul_one, hvv])
      map_mul' := fun s t => Subtype.ext (by
        change (s : G) * t * (v * ((s : G) * t) * v) =
          (s : G) * (v * s * v) * (t * (v * t * v))
        have hc := elemAbelian_comm hE t.2 (hvE s s.2)
        have h1 : v * ((s : G) * t) * v = (v * s * v) * (v * t * v) := by
          calc v * ((s : G) * t) * v = v * s * (v * v) * t * v := by rw [hvv]; group
            _ = (v * s * v) * (v * t * v) := by group
        rw [h1]
        calc (s : G) * t * ((v * s * v) * (v * t * v))
            = s * (t * (v * s * v)) * (v * t * v) := by group
          _ = s * ((v * s * v) * t) * (v * t * v) := by rw [hc]
          _ = s * (v * s * v) * (t * (v * t * v)) := by group) }
  set F := E ⊓ centralizer ({v} : Set G) with hF
  have hmemF : ∀ e : E, v * (e : G) * v = e → (e : G) ∈ F := fun e he => by
    refine Subgroup.mem_inf.mpr ⟨e.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc (e : G) * v = (v * e * v) * v := by rw [he]
      _ = v * e * (v * v) := by group
      _ = v * e := by rw [hvv, mul_one]
  have hker : φ.ker ≤ F.subgroupOf E := fun e he => by
    have h1 : (e : G) * (v * e * v) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp he)
    rw [Subgroup.mem_subgroupOf]
    apply hmemF
    rw [eq_inv_of_mul_eq_one_right h1, elemAbelian_inv hE e.2]
  have hrange : φ.range ≤ F.subgroupOf E := by
    rintro _ ⟨e, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    apply hmemF
    change v * ((e : G) * (v * e * v)) * v = (e : G) * (v * e * v)
    have hc := elemAbelian_comm hE e.2 (hvE e e.2)
    calc v * ((e : G) * (v * e * v)) * v = v * ((v * e * v) * e) * v := by rw [hc]
      _ = (v * v) * e * v * e * v := by group
      _ = e * v * e * v := by rw [hvv, one_mul]
      _ = e * (v * e * v) := by group
  have hcardF : Nat.card (F.subgroupOf E) = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h8 : 8 ≤ Nat.card F * Nat.card F := by
    rw [← hcardF, ← hcard, ← Subgroup.card_mul_index φ.ker, Subgroup.index_ker]
    exact Nat.mul_le_mul (Subgroup.card_le_of_le hker) (Subgroup.card_le_of_le hrange)
  have hdvd : Nat.card F ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← hcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨m, _hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hm'] at h8 ⊢
  interval_cases m <;> simp_all

theorem false_of_mem_normal_E8 {𝒮 : Sylow 2 G} {E : Subgroup G}
    (hE𝒮 : E ≤ (𝒮 : Subgroup G)) (hEn : (E.subgroupOf (𝒮 : Subgroup G)).Normal)
    (hEc : Nat.card E = 8) (hG2 : 2 ^ 11 ∣ Nat.card G) {c : G} (hc : c ∈ E)
    (hbound : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ centralizer ({c} : Set G) →
      Nat.card Q ≤ 2 ^ 7) : False := by
  have hSnorm : (𝒮 : Subgroup G) ≤ normalizer (E : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hE𝒮).mp hEn
  let C : Subgroup G := (𝒮 : Subgroup G) ⊓ centralizer ({c} : Set G)
  have hCc : C ≤ centralizer ({c} : Set G) := inf_le_right
  have hCp : IsPGroup 2 C := 𝒮.isPGroup'.to_le inf_le_left
  have hCbound : Nat.card C ≤ 2 ^ 7 := hbound C hCp hCc
  have hcardC' : Nat.card (C.subgroupOf (𝒮 : Subgroup G)) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  let φ : ↥𝒮 →* MulAut ↥E := E.normalizerMonoidHom.comp (Subgroup.inclusion hSnorm)
  letI : MulAction ↥𝒮 ↥E := MulAction.compHom (↥E) φ
  have hsmul : ∀ (n : ↥𝒮) (x : ↥E),
      ((n • x : ↥E) : G) = (n : G) * (x : G) * (n : G)⁻¹ := fun n x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe E (Subgroup.inclusion hSnorm n) x
  have hstab : MulAction.stabilizer ↥𝒮 (⟨c, hc⟩ : ↥E) = C.subgroupOf (𝒮 : Subgroup G) := by
    ext n
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      refine ⟨n.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h' := congrArg (fun e : ↥E => (e : G)) h
      simp only [hsmul] at h'
      calc (n : G) * c = ((n : G) * c * (n : G)⁻¹) * n := by group
        _ = c * n := by rw [h']
    · intro h
      apply Subtype.ext
      rw [hsmul]
      have h' := Subgroup.mem_centralizer_singleton_iff.mp h.2
      rw [h', mul_inv_cancel_right]
  have hidx : (C.subgroupOf (𝒮 : Subgroup G)).index =
      (MulAction.orbit ↥𝒮 (⟨c, hc⟩ : ↥E)).ncard := by
    rw [← hstab]
    exact MulAction.index_stabilizer ↥𝒮 _
  have horbit_le : (MulAction.orbit ↥𝒮 (⟨c, hc⟩ : ↥E)).ncard ≤ Nat.card ↥E := by
    rw [← Set.ncard_univ (α := ↥E)]
    exact Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
  have hidx_le : (C.subgroupOf (𝒮 : Subgroup G)).index ≤ 8 := by
    rw [hidx, ← hEc]
    exact horbit_le
  have hcardS_le : Nat.card (𝒮 : Subgroup G) ≤ 2 ^ 10 := by
    rw [← Subgroup.card_mul_index (C.subgroupOf (𝒮 : Subgroup G))]
    calc Nat.card (C.subgroupOf (𝒮 : Subgroup G)) * (C.subgroupOf (𝒮 : Subgroup G)).index
        ≤ Nat.card C * 8 := Nat.mul_le_mul hcardC'.le hidx_le
      _ ≤ 2 ^ 7 * 8 := Nat.mul_le_mul hCbound le_rfl
      _ = 2 ^ 10 := by norm_num
  have hfac : 11 ≤ (Nat.card G).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization (Nat.card_pos (α := G)).ne').mp hG2
  have hcardS_ge : 2 ^ 11 ≤ Nat.card (𝒮 : Subgroup G) := by
    rw [show Nat.card (𝒮 : Subgroup G) = 2 ^ (Nat.card G).factorization 2 from
      Sylow.card_eq_multiplicity 𝒮]
    exact Nat.pow_le_pow_right (by norm_num) hfac
  have hcontra : (2 : ℕ) ^ 11 ≤ 2 ^ 10 := le_trans hcardS_ge hcardS_le
  norm_num at hcontra

theorem card_le_of_isPGroup_le_centralizer_conj {S : Subgroup G} {t : G}
    (hSH : S ≤ centralizer ({t} : Set G)) (hS : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.relIndex (centralizer ({t} : Set G))) (hcardS : Nat.card S = 2 ^ 7) (g : G)
    {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQc : Q ≤ centralizer ({g * t * g⁻¹} : Set G)) :
    Nat.card Q ≤ 2 ^ 7 := by
  let Q' : Subgroup G := Q.map (MulAut.conj g⁻¹).toMonoidHom
  have hQ'p : IsPGroup 2 Q' := hQ.map (MulAut.conj g⁻¹).toMonoidHom
  have hQ'c : Q' ≤ centralizer ({t} : Set G) := by
    rintro x hx
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hqcomm : q * (g * t * g⁻¹) = (g * t * g⁻¹) * q :=
      Subgroup.mem_centralizer_singleton_iff.mp (hQc hq)
    have hconj : (MulAut.conj g⁻¹) (g * t * g⁻¹) = t := by
      rw [MulAut.conj_apply]
      group
    have key : (MulAut.conj g⁻¹) q * t = t * (MulAut.conj g⁻¹) q := by
      have h := congrArg (MulAut.conj g⁻¹) hqcomm
      simpa only [map_mul, hconj] using h
    exact key
  obtain ⟨k, _hkH, hk⟩ := exists_conj_le_of_isPGroup hQ'c hQ'p hSH hS hSi
  have hmap : Q'.map (MulAut.conj k).toMonoidHom ≤ S := by
    rintro _ ⟨q, hq, rfl⟩
    simpa [MulAut.conj_apply] using hk q hq
  calc Nat.card Q = Nat.card Q' :=
        (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).symm
    _ = Nat.card (Q'.map (MulAut.conj k).toMonoidHom) :=
        (Subgroup.card_map_of_injective (MulAut.conj k).injective).symm
    _ ≤ Nat.card S := Subgroup.card_le_of_le hmap
    _ = 2 ^ 7 := hcardS

theorem four_le_card_inf_centralizer {E 𝒮 : Subgroup G} (hE𝒮 : E ≤ 𝒮)
    (hEn : (E.subgroupOf 𝒮).Normal) (hEe : CFSG.Open.IsElemAbelian 2 E)
    (hEc : Nat.card E = 8) {t : G} (ht𝒮 : t ∈ 𝒮) (ht2 : t * t = 1) :
    4 ≤ Nat.card ↥(E ⊓ centralizer ({t} : Set G)) := by
  have hnorm : ∀ e ∈ E, t * e * t⁻¹ ∈ E := by
    intro e he
    have hn : (⟨e, hE𝒮 he⟩ : ↥𝒮) ∈ E.subgroupOf 𝒮 := by
      rw [Subgroup.mem_subgroupOf]; exact he
    have h := hEn.conj_mem (⟨e, hE𝒮 he⟩ : ↥𝒮) hn (⟨t, ht𝒮⟩ : ↥𝒮)
    simpa using Subgroup.mem_subgroupOf.mp h
  exact four_le_card_inf_centralizer_of_card_eight hEe hEc hnorm ht2

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
