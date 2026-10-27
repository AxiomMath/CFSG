module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L34GL32
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L34Size

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped MatrixGroups

section Generic

variable {G : Type} [Group G]

theorem eq_one_of_isPGroup_of_odd {H : Type} [Group H] (hH : IsPGroup 2 H) {g : H}
    (hg : Odd (orderOf g)) : g = 1 := by
  obtain ⟨k, hk⟩ := hH g
  have hd : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (orderOf g) (2 ^ k) :=
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hg)).symm
  have h1 : orderOf g = 1 := Nat.Coprime.eq_one_of_dvd hcop hd
  exact orderOf_eq_one_iff.mp h1

theorem mem_normalizer_of_forall_commute {U : Subgroup G} {b : G} (h : ∀ v ∈ U, b * v = v * b) :
    b ∈ normalizer (U : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro u
  have hc : ∀ v ∈ U, b * v * b⁻¹ = v := fun v hv => by
    calc b * v * b⁻¹ = (v * b) * b⁻¹ := by rw [← h v hv]
      _ = v := by group
  constructor
  · intro hu
    rw [hc u hu]
    exact hu
  · intro hu
    have hv := h _ hu
    have h2 : b⁻¹ * (b * u * b⁻¹) * b = b * u * b⁻¹ := by
      calc b⁻¹ * (b * u * b⁻¹) * b = b⁻¹ * ((b * u * b⁻¹) * b) := by group
        _ = b⁻¹ * (b * (b * u * b⁻¹)) := by rw [← hv]
        _ = b * u * b⁻¹ := by group
    have e : u = b⁻¹ * (b * u * b⁻¹) * b := by group
    rw [e, h2]
    exact hu

theorem conjAut_pow {K : Subgroup G} {b : G} (α : MulAut ↥K)
    (hα : ∀ k : ↥K, ((α k : ↥K) : G) = b⁻¹ * (k : G) * b) (n : ℕ) (k : ↥K) :
    (((α ^ n) k : ↥K) : G) = (b ^ n)⁻¹ * (k : G) * b ^ n := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, hα, pow_succ']
    group

theorem odd_orderOf_conjAut {K : Subgroup G} {b : G} (α : MulAut ↥K)
    (hα : ∀ k : ↥K, ((α k : ↥K) : G) = b⁻¹ * (k : G) * b) (hb : Odd (orderOf b)) :
    Odd (orderOf α) := by
  have h1 : α ^ orderOf b = 1 := by
    refine MulEquiv.ext fun k => Subtype.ext ?_
    rw [conjAut_pow α hα, pow_orderOf_eq_one]
    simp
  exact Odd.of_dvd_nat hb (orderOf_dvd_of_pow_eq_one h1)

end Generic

section Main

variable {G : Type} [Group G] [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}

section G2

variable (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3) (hI : Inputs2436)
  (hK : A3A3K T M H S L s x z₁ z₂ K) (hc : blockU2 L s ≤ Subgroup.centralizer (K : Set G))
include hD h27_1 hI hK hc

theorem A3A3K.l27Aut_K : L27Aut ↥K := by
  obtain ⟨e⟩ := hK.nonempty_psl27 hD h27_1 hI hc
  exact l27AutFact ↥K ⟨e⟩

theorem A3A3K.l27Aut_Ks
    : L27Aut ↥(conjR K s) := by
  obtain ⟨e⟩ := hK.nonempty_psl27 hD h27_1 hI hc
  obtain ⟨ι, -⟩ := exists_conjR_equiv K s
  exact l27AutFact ↥(conjR K s) ⟨ι.symm.trans e⟩

theorem A3A3K.eq_one_of_odd_of_mem_B
    {b : G} (hbz : b ∈ centralizerElem z₂)
    (hbK : b ∈ Subgroup.centralizer (K : Set G)) (hodd : Odd (orderOf b)) : b = 1 := by
  have hUK : blockU L ≤ K := hK.isA4.le.trans hK.L_le_K
  have hbU : b ∈ normalizer (blockU L : Set G) :=
    mem_normalizer_of_forall_commute fun v hv => (Subgroup.mem_centralizer_iff.mp hbK v (hUK hv)).symm
  have hbN : b ∈ normalizer ((conjR K s : Subgroup G) : Set G) :=
    hK.normalizer_blockU_le hD h27_1 hI hc hbU
  obtain ⟨β, hβ⟩ := exists_conjAut hbN
  have hβodd := odd_orderOf_conjAut β hβ hodd
  obtain ⟨k', hk'⟩ := (hK.l27Aut_Ks hD h27_1 hI hc).isInner_of_odd hβodd
  have hcK' : ∀ y ∈ conjR K s, y * (b * (k' : G)) = (b * (k' : G)) * y := by
    intro y hy
    have h1 := congrArg Subtype.val (hk' ⟨y, hy⟩)
    rw [hβ] at h1
    have h2 : b⁻¹ * y * b = (k' : G) * y * (k' : G)⁻¹ := h1
    calc y * (b * (k' : G)) = b * (b⁻¹ * y * b) * (k' : G) := by group
      _ = b * ((k' : G) * y * (k' : G)⁻¹) * (k' : G) := by rw [h2]
      _ = (b * (k' : G)) * y := by group
  have hcK : ∀ y ∈ K, y * (b * (k' : G)) = (b * (k' : G)) * y := by
    intro y hy
    have h1 : y * b = b * y := Subgroup.mem_centralizer_iff.mp hbK y hy
    have h2 : y * (k' : G) = (k' : G) * y := hK.comm_K_Ks hD h27_1 hI hc y hy k' k'.2
    calc y * (b * (k' : G)) = (y * b) * (k' : G) := by group
      _ = b * (y * (k' : G)) := by rw [h1]; group
      _ = b * ((k' : G) * y) := by rw [h2]
      _ = (b * (k' : G)) * y := by group
  have hcN : b * (k' : G) ∈ Subgroup.centralizer ((K ⊔ conjR K s : Subgroup G) : Set G) := by
    have hle : (K ⊔ conjR K s : Subgroup G) ≤ centralizerElem (b * (k' : G)) :=
      sup_le (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hcK y hy))
        (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hcK' y hy))
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hn)
  rw [hK.centralizer_sup_eq_bot hD h27_1 hI hc, Subgroup.mem_bot] at hcN
  have hbk : b = (k' : G)⁻¹ := by
    calc b = (b * (k' : G)) * (k' : G)⁻¹ := by group
      _ = (k' : G)⁻¹ := by rw [hcN]; group
  have hbK' : b ∈ conjR K s := by
    rw [hbk]; exact (conjR K s).inv_mem k'.2
  have hz₂K' : z₂ ∈ conjR K s := hK.z₂_mem_conjR
  have hz₂1 : (⟨z₂, hz₂K'⟩ : ↥(conjR K s)) ≠ 1 := fun h => hK.toA3A3x.z₂_ne (congrArg Subtype.val h)
  have hz₂ord : orderOf (⟨z₂, hz₂K'⟩ : ↥(conjR K s)) = 2 :=
    orderOf_eq_prime (Subtype.ext (by simpa using hK.toA3A3x.sq₂)) hz₂1
  have hcent := (hK.l2pData_Ks hD h27_1 hI hc).cent_two _ hz₂ord
  let d : ↥(conjR K s) := ⟨b, hbK'⟩
  have hd : d ∈ Subgroup.centralizer ({(⟨z₂, hz₂K'⟩ : ↥(conjR K s))} : Set ↥(conjR K s)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hbz)
  have hd1 : (⟨d, hd⟩ : ↥(Subgroup.centralizer
      ({(⟨z₂, hz₂K'⟩ : ↥(conjR K s))} : Set ↥(conjR K s)))) = 1 := by
    apply eq_one_of_isPGroup_of_odd hcent
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact hodd
  have : d = 1 := congrArg Subtype.val hd1
  exact congrArg Subtype.val this

theorem A3A3K.mem_K_of_odd
    {g : G} (hg : g ∈ centralizerElem z₂) (hodd : Odd (orderOf g)) :
    g ∈ K := by
  have hgN : g ∈ normalizer (K : Set G) := hK.K_norm hg
  obtain ⟨α, hα⟩ := exists_conjAut hgN
  have hαodd := odd_orderOf_conjAut α hα hodd
  obtain ⟨k, hk⟩ := (hK.l27Aut_K hD h27_1 hI hc).isInner_of_odd hαodd
  have hbK : g * (k : G) ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg Subtype.val (hk ⟨y, hy⟩)
    rw [hα] at h1
    have h2 : g⁻¹ * y * g = (k : G) * y * (k : G)⁻¹ := h1
    calc y * (g * (k : G)) = g * (g⁻¹ * y * g) * (k : G) := by group
      _ = g * ((k : G) * y * (k : G)⁻¹) * (k : G) := by rw [h2]
      _ = (g * (k : G)) * y := by group
  have hKG : K ≤ centralizerElem z₂ := hK.K_comp.1
  have hbz : g * (k : G) ∈ centralizerElem z₂ := mul_mem hg (hKG k.2)
  set b : G := g * (k : G) with hbdef
  have hgb : g = b * (k : G)⁻¹ := by rw [hbdef]; group
  have hcomm : Commute b (k : G)⁻¹ := by
    have := Subgroup.mem_centralizer_iff.mp hbK ((k : G)⁻¹) (K.inv_mem k.2)
    exact this.symm
  obtain ⟨r, hrdef⟩ : ∃ r, orderOf g = r := ⟨_, rfl⟩
  have hr : g ^ r = 1 := by rw [← hrdef]; exact pow_orderOf_eq_one g
  have hbr : b ^ r = (k : G) ^ r := by
    have hr' := hr
    rw [hgb, hcomm.mul_pow, inv_pow] at hr'
    exact mul_inv_eq_one.mp hr'
  have hbrK : b ^ r ∈ K := by rw [hbr]; exact pow_mem k.2 _
  have hbrC : b ^ r ∈ Subgroup.centralizer (K : Set G) := Subgroup.pow_mem _ hbK _
  have hbr1 : b ^ r = 1 :=
    BenderBranch.eq_one_of_commute_of_simple hK.isSimpleGroup hK.nonabelian hbrK fun y hy =>
      (Subgroup.mem_centralizer_iff.mp hbrC y hy)
  have hbodd : Odd (orderOf b) :=
    Odd.of_dvd_nat (hrdef ▸ hodd : Odd r) (orderOf_dvd_of_pow_eq_one hbr1)
  have hb1 : b = 1 := hK.eq_one_of_odd_of_mem_B hD h27_1 hI hc hbz hbK hbodd
  rw [hgb, hb1, one_mul]
  exact K.inv_mem k.2

theorem A3A3K.mem_conjR_K_of_odd
    {h g : G} (hg : g ∈ centralizerElem (h⁻¹ * z₂ * h))
    (hodd : Odd (orderOf g)) : g ∈ conjR K h := by
  have hg' : h * g * h⁻¹ ∈ centralizerElem z₂ := by
    have hg0 := Subgroup.mem_centralizer_singleton_iff.mp hg
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc h * g * h⁻¹ * z₂ = h * (g * (h⁻¹ * z₂ * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * z₂ * h) * g) * h⁻¹ := by rw [hg0]
      _ = z₂ * (h * g * h⁻¹) := by group
  have hodd' : Odd (orderOf (h * g * h⁻¹)) := by
    have h1 := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective g
    have h2 : (MulAut.conj h).toMonoidHom g = h * g * h⁻¹ := by simp
    rw [h2] at h1
    rw [h1]
    exact hodd
  have := hK.mem_K_of_odd hD h27_1 hI hc hg' hodd'
  exact mem_conjR.mpr this

end G2

end Main

end CFSG.QuasithinUnique.DoubleA3
