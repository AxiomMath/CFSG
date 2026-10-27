module

public import CFSG.GH74.RouteH
public import CFSG.GH74.Filter.Final
public import CFSG.GH74.OrderForm

public section

namespace CFSG.GH74

theorem s_filter :
    S_filter :=
  Filter.filter

theorem gh74_of_routeH_filter
    (hW : S_walterNative) (hQ : S_QTKE_Gen4)
    (hRE : S_restrictedEven) (hGen : S_generic) (hSO : S_specialOdd) : GH74Statement :=
  gh74_of_routeH hW hQ s_filter hRE hGen hSO

theorem modelsForm_of_gh74Statement (h : GH74Statement) : ModelsFormStatement :=
  fun G _ _ _ hnonab hrank hsect => h G inferInstance hnonab hrank hsect

theorem milestone_forms_of_inputs
    (hW : S_walterNative) (hQ : S_QTKE_Gen4)
    (hRE : S_restrictedEven) (hGen : S_generic) (hSO : S_specialOdd) :
    ModelsFormStatement ∧ OrderFormStatement :=
  have h := modelsForm_of_gh74Statement (gh74_of_routeH_filter hW hQ hRE hGen hSO)
  ⟨h, orderForm_of_modelsForm h⟩

end CFSG.GH74
