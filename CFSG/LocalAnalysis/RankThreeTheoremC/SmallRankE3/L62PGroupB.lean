module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralPerfectLifts
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {H : Type} [Group H] [Finite H]

private theorem l62_card_mul_le_card_sup {K X : Subgroup H} (h : K ⊓ X = ⊥) :
    Nat.card K * Nat.card X ≤ Nat.card ↥(K ⊔ X) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun a : K × X => (⟨(a.1 : H) * (a.2 : H), Subgroup.mul_mem_sup a.1.2 a.2.2⟩ : ↥(K ⊔ X)))
    ?_
  rintro ⟨a, b⟩ ⟨a', b'⟩ hab
  have h1 : (a : H) * b = a' * b' := congrArg Subtype.val hab
  have h2 : (a' : H)⁻¹ * a = (b' : H) * (b : H)⁻¹ := by
    calc (a' : H)⁻¹ * a = (a' : H)⁻¹ * (a * b) * (b : H)⁻¹ := by group
      _ = (a' : H)⁻¹ * (a' * b') * (b : H)⁻¹ := by rw [h1]
      _ = (b' : H) * (b : H)⁻¹ := by group
  have h3 : (a' : H)⁻¹ * a ∈ K ⊓ X :=
    ⟨K.mul_mem (K.inv_mem a'.2) a.2, h2 ▸ X.mul_mem b'.2 (X.inv_mem b.2)⟩
  rw [h, Subgroup.mem_bot, inv_mul_eq_one] at h3
  have h4 : (b : H) = b' := by
    rw [← h3] at h1
    exact mul_left_cancel h1
  exact Prod.ext (Subtype.ext h3.symm) (Subtype.ext h4)

private theorem l62_isElemAbelian_mono {p : ℕ} {E F : Subgroup H} (hFE : F ≤ E)
    (hE : IsElemAbelian p E) : IsElemAbelian p F := by
  refine ⟨⟨⟨fun u v => ?_⟩⟩, fun g hg => hE.2 g (hFE hg)⟩
  have h : (u : H) * (v : H) = (v : H) * (u : H) :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨(u : H), hFE u.2⟩ ⟨(v : H), hFE v.2⟩)
  exact Subtype.ext h

private theorem l62_comm_zpowers {x : H} : ∀ a ∈ zpowers x, ∀ b ∈ zpowers x, a * b = b * a := by
  intro a ha b hb
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp ha
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hb
  exact (Commute.zpow_zpow_self x m n).eq

private theorem l62_isElemAbelian_zpowers {p : ℕ} {x : H} (hx : x ^ p = 1) :
    IsElemAbelian p (zpowers x) := by
  refine ⟨⟨⟨fun u v => Subtype.ext (l62_comm_zpowers (u : H) u.2 (v : H) v.2)⟩⟩, ?_⟩
  intro g hg
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

private theorem l62_zpowers_eq {p : ℕ} [Fact p.Prime] {y c : H} (hy : y ^ p = 1) (hc : c ^ p = 1)
    (hy1 : y ≠ 1) (hc1 : c ≠ 1) (h : y ∈ zpowers c) : zpowers y = zpowers c :=
  eq_of_le_of_card_ge (zpowers_le.2 h) (by
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hy hy1, orderOf_eq_prime hc hc1])

private theorem l62_isElemAbelian_sup {p : ℕ} {A B : Subgroup H} (hA : IsElemAbelian p A)
    (hB : IsElemAbelian p B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian p (A ⊔ B) := by
  have hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  have hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := fun b hb b' hb' =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨b, hb⟩ ⟨b', hb'⟩)
  have hcA : A ⊔ B ≤ Subgroup.centralizer (A : Set H) := by
    refine sup_le ?_ ?_
    · intro a ha
      exact Subgroup.mem_centralizer_iff.mpr fun h hh => hAc h hh a ha
    · intro b hb
      exact Subgroup.mem_centralizer_iff.mpr fun h hh => hAB h hh b hb
  have hcB : A ⊔ B ≤ Subgroup.centralizer (B : Set H) := by
    refine sup_le ?_ ?_
    · intro a ha
      exact Subgroup.mem_centralizer_iff.mpr fun h hh => (hAB a ha h hh).symm
    · intro b hb
      exact Subgroup.mem_centralizer_iff.mpr fun h hh => hBc h hh b hb
  have hcS : A ⊔ B ≤ Subgroup.centralizer ((A ⊔ B : Subgroup H) : Set H) := by
    refine sup_le ?_ ?_
    · intro a ha
      refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      exact (Subgroup.mem_centralizer_iff.mp (hcA (SetLike.mem_coe.mp hh)) a ha).symm
    · intro b hb
      refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      exact (Subgroup.mem_centralizer_iff.mp (hcB (SetLike.mem_coe.mp hh)) b hb).symm
  have hcomm : ∀ u ∈ A ⊔ B, ∀ v ∈ A ⊔ B, u * v = v * u := fun u hu v hv =>
    (Subgroup.mem_centralizer_iff.mp (hcS hu) v (SetLike.mem_coe.mpr hv)).symm
  have e : A ⊔ B = ⨆ i : Bool, cond i A B := sup_eq_iSup A B
  refine ⟨⟨⟨fun u v => Subtype.ext (hcomm u u.2 v v.2)⟩⟩, ?_⟩
  intro g hg
  have hg' := hg
  rw [e] at hg'
  refine Subgroup.iSup_induction' (fun i : Bool => cond i A B)
    (C := fun g _ => g ^ p = 1) ?_ (one_pow p) ?_ hg'
  · intro i g hg
    cases i
    · exact hB.2 g hg
    · exact hA.2 g hg
  · intro a b ha hb iha ihb
    have hc : Commute a b := hcomm a (e ▸ ha) b (e ▸ hb)
    rw [hc.mul_pow, iha, ihb, mul_one]

private theorem l62_card_cent_le {p : ℕ} [Fact p.Prime] {S : Subgroup H} {x : H}
    (hx3 : x ^ p = 1) (hxS : x ∈ S)
    (hrank : ∀ E : Subgroup H, E ≤ S → IsElemAbelian p E → (∀ e ∈ E, e * x = x * e) →
      Nat.card E ≤ p ^ 2)
    {E : Subgroup H} (hEP : E ≤ S) (hE : IsElemAbelian p E) (hxE : x ∉ E) :
    Nat.card ↥(E ⊓ centralizer ({x} : Set H)) ≤ p := by
  have hp : p.Prime := Fact.out
  set K : Subgroup H := E ⊓ centralizer ({x} : Set H)
  have hxne : x ≠ 1 := fun h1 => hxE (h1 ▸ E.one_mem)
  have hXc : Nat.card (zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hxne]
  have hKX : K ⊓ zpowers x = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    by_contra hg1
    have hgE : g ∈ E := hg.1.1
    have hgp : g ^ p = 1 := hE.2 g hgE
    have hzp := l62_zpowers_eq hgp hx3 hg1 hxne hg.2
    apply hxE
    have : x ∈ zpowers g := by rw [hzp]; exact mem_zpowers x
    exact zpowers_le.mpr hgE this
  have hKe : IsElemAbelian p K := l62_isElemAbelian_mono inf_le_left hE
  have hXe : IsElemAbelian p (zpowers x) := l62_isElemAbelian_zpowers hx3
  have hKXc : ∀ a ∈ K, ∀ b ∈ zpowers x, a * b = b * a := by
    intro a ha b hb
    have hxa : x * a = a * x := (mem_centralizer_singleton_iff.mp ha.2).symm
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hb
    exact ((Commute.zpow_right (show Commute a x from hxa.symm) n).eq)
  have hFe : IsElemAbelian p (K ⊔ zpowers x) := l62_isElemAbelian_sup hKe hXe hKXc
  have hFP : K ⊔ zpowers x ≤ S :=
    sup_le (inf_le_left.trans hEP) (zpowers_le.mpr hxS)
  have hFx : ∀ e ∈ K ⊔ zpowers x, e * x = x * e := fun e he =>
    congrArg Subtype.val (hFe.1.is_comm.comm ⟨e, he⟩
      ⟨x, Subgroup.mem_sup_right (mem_zpowers x)⟩)
  have hF2 := hrank _ hFP hFe hFx
  have hcard := l62_card_mul_le_card_sup hKX
  rw [hXc] at hcard
  have h1 : Nat.card K * p ≤ p * p := by
    calc Nat.card K * p ≤ Nat.card ↥(K ⊔ zpowers x) := hcard
      _ ≤ p ^ 2 := hF2
      _ = p * p := by ring
  exact Nat.le_of_mul_le_mul_right h1 hp.pos

private theorem l62_card_le_sq_of_comm {p : ℕ} [Fact p.Prime] {S : Subgroup H} {x z : H}
    (hx3 : x ^ p = 1) (hxS : x ∈ S) (hz : z ^ p = 1) (hz1 : z ≠ 1)
    (hzc : ∀ g ∈ S, g * z = z * g)
    (hrank : ∀ E : Subgroup H, E ≤ S → IsElemAbelian p E → (∀ e ∈ E, e * x = x * e) →
      Nat.card E ≤ p ^ 2)
    {E : Subgroup H} (hEP : E ≤ S) (hE : IsElemAbelian p E)
    (hcomm : ∀ e ∈ E, x * e * x⁻¹ * e⁻¹ ∈ zpowers z) : Nat.card E ≤ p ^ 2 := by
  have hp : p.Prime := Fact.out
  by_cases hxE : x ∈ E
  · have hc : ∀ e ∈ E, e * x = x * e := fun e he =>
      congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨x, hxE⟩)
    exact hrank E hEP hE hc
  · have hzcent : ∀ w ∈ zpowers z, ∀ g ∈ S, g * w = w * g := by
      intro w hw g hg
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hw
      exact (Commute.zpow_right (show Commute g z from hzc g hg) n).eq
    let δ : ↥E →* ↥(zpowers z) := MonoidHom.mk' (fun e => ⟨x * e * x⁻¹ * (e : H)⁻¹, hcomm e e.2⟩)
      (fun e e' => by
        apply Subtype.ext
        have hc : ((e : H)) * (x * e' * x⁻¹ * (e' : H)⁻¹) = (x * e' * x⁻¹ * (e' : H)⁻¹) * e :=
          hzcent _ (hcomm e' e'.2) e (hEP e.2)
        change x * ((e : H) * e') * x⁻¹ * ((e : H) * e')⁻¹ =
          (x * e * x⁻¹ * (e : H)⁻¹) * (x * e' * x⁻¹ * (e' : H)⁻¹)
        calc x * ((e : H) * e') * x⁻¹ * ((e : H) * e')⁻¹
            = x * e * x⁻¹ * (x * e' * x⁻¹ * (e' : H)⁻¹) * (e : H)⁻¹ := by group
          _ = x * e * x⁻¹ * ((e : H)⁻¹ * ((e : H) * (x * e' * x⁻¹ * (e' : H)⁻¹)) * (e : H)⁻¹) := by
            group
          _ = x * e * x⁻¹ * ((e : H)⁻¹ * ((x * e' * x⁻¹ * (e' : H)⁻¹) * e) * (e : H)⁻¹) := by
            rw [hc]
          _ = (x * e * x⁻¹ * (e : H)⁻¹) * (x * e' * x⁻¹ * (e' : H)⁻¹) := by group)
    have h1 := Subgroup.card_ker_mul_card_range δ
    have hker : Nat.card δ.ker ≤ Nat.card ↥(E ⊓ centralizer ({x} : Set H)) := by
      have hmem : ∀ m : δ.ker, ((m : ↥E) : H) ∈ E ⊓ centralizer ({x} : Set H) := by
        intro m
        refine ⟨(m : ↥E).2, ?_⟩
        have hm : δ (m : ↥E) = 1 := m.2
        have h2 : x * ((m : ↥E) : H) * x⁻¹ * ((m : ↥E) : H)⁻¹ = 1 :=
          congrArg Subtype.val hm
        show ((m : ↥E) : H) ∈ centralizer ({x} : Set H)
        rw [mem_centralizer_singleton_iff]
        symm
        have h3 := mul_inv_eq_one.mp h2
        rw [mul_inv_eq_iff_eq_mul] at h3
        exact h3
      refine Nat.card_le_card_of_injective (fun m => ⟨((m : ↥E) : H), hmem m⟩) ?_
      intro m n hmn
      exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hmn))
    have hrange : Nat.card δ.range ≤ p := by
      have : Nat.card δ.range ≤ Nat.card ↥(zpowers z) := Subgroup.card_le_card_group _
      rwa [Nat.card_zpowers, orderOf_eq_prime hz hz1] at this
    calc Nat.card E = Nat.card δ.ker * Nat.card δ.range := h1.symm
      _ ≤ p * p :=
        Nat.mul_le_mul (hker.trans (l62_card_cent_le hx3 hxS hrank hEP hE hxE)) hrange
      _ = p ^ 2 := by ring

private theorem l62_zpowers_central {S : Subgroup H} {z : H} (hzc : ∀ g ∈ S, g * z = z * g)
    {w g : H} (hw : w ∈ zpowers z) (hg : g ∈ S) : g * w = w * g := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hw
  exact (Commute.zpow_right (show Commute g z from hzc g hg) n).eq

private theorem l62_comm_mul_mem {S : Subgroup H} {x z : H} (hzc : ∀ g ∈ S, g * z = z * g)
    {e e' : H} (he : e ∈ S) (he1 : x * e * x⁻¹ * e⁻¹ ∈ zpowers z)
    (he2 : x * e' * x⁻¹ * e'⁻¹ ∈ zpowers z) :
    x * (e * e') * x⁻¹ * (e * e')⁻¹ ∈ zpowers z := by
  have hc : e * (x * e' * x⁻¹ * e'⁻¹) = (x * e' * x⁻¹ * e'⁻¹) * e :=
    l62_zpowers_central hzc he2 he
  have : x * (e * e') * x⁻¹ * (e * e')⁻¹ =
      (x * e * x⁻¹ * e⁻¹) * (x * e' * x⁻¹ * e'⁻¹) := by
    calc x * (e * e') * x⁻¹ * (e * e')⁻¹
        = (x * e * x⁻¹ * e⁻¹) * (e * (x * e' * x⁻¹ * e'⁻¹) * e⁻¹) := by group
      _ = (x * e * x⁻¹ * e⁻¹) * ((x * e' * x⁻¹ * e'⁻¹) * e * e⁻¹) := by rw [hc]
      _ = (x * e * x⁻¹ * e⁻¹) * (x * e' * x⁻¹ * e'⁻¹) := by group
  rw [this]
  exact (zpowers z).mul_mem he1 he2

theorem l62_card_le_nine_of_comm {S : Subgroup H} {x z : H} (hxS : x ∈ S) (hx3 : x ^ 3 = 1)
    (hzS : z ∈ S) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) (hzc : ∀ g ∈ S, g * z = z * g)
    (hrank : ∀ E : Subgroup H, E ≤ S → IsElemAbelian 3 E → (∀ e ∈ E, e * x = x * e) →
      Nat.card E ≤ 3 ^ 2)
    {E : Subgroup H} (hES : E ≤ S) (hE : IsElemAbelian 3 E)
    (hcomm : ∀ e ∈ E, x * e * x⁻¹ * e⁻¹ ∈ zpowers z) : Nat.card E ≤ 3 ^ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact l62_card_le_sq_of_comm (p := 3) hx3 hxS hz3 hz1 hzc hrank hES hE hcomm

theorem l62_comm_mem_sup {S : Subgroup H} {x z : H} (hzc : ∀ g ∈ S, g * z = z * g)
    {V V' : Subgroup H} (hV : V ≤ S) (hV' : V' ≤ S)
    (h1 : ∀ e ∈ V, x * e * x⁻¹ * e⁻¹ ∈ zpowers z)
    (h2 : ∀ e ∈ V', x * e * x⁻¹ * e⁻¹ ∈ zpowers z) :
    ∀ e ∈ V ⊔ V', x * e * x⁻¹ * e⁻¹ ∈ zpowers z := by
  intro e he
  have hE : V ⊔ V' = ⨆ i : Bool, cond i V V' := sup_eq_iSup V V'
  have heS : ∀ e ∈ V ⊔ V', e ∈ S := fun e he => sup_le hV hV' he
  have he' := he
  rw [hE] at he'
  refine Subgroup.iSup_induction' (fun i : Bool => cond i V V')
    (C := fun e _ => x * e * x⁻¹ * e⁻¹ ∈ zpowers z) ?_ ?_ ?_ he'
  · intro i e he
    cases i
    · exact h2 e he
    · exact h1 e he
  · simpa using (zpowers z).one_mem
  · intro a b ha hb iha ihb
    exact l62_comm_mul_mem hzc (heS a (hE ▸ ha)) iha ihb

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
